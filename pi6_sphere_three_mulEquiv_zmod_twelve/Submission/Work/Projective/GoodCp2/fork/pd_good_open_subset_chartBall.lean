import Mathlib
import Submission.Work.Cohomology.pd_good
import Submission.Work.Cohomology.pd_good_iUnion
import Submission.Work.Projective.GoodCp2.fork.pd_good_list_pieces
import Submission.Work.Cohomology.euclid_open_monotone_finiteUnions_convex

set_option synthInstance.maxHeartbeats 400000

/-!
# `Good` for an open subset of a coordinate ball

`Work.Cohomology.Good N c W hW` is the elementwise form of Poincaré–Lefschetz duality for the open
set `W` (see `Work.Cohomology.pd_good`); `Work.Cohomology.pd_good_convex` proves it for a single
convex coordinate piece and `Work.Cohomology.pd_good_list_pieces` for finite unions of such pieces.

Here we pass to an *arbitrary* open subset `U` of a coordinate ball: in the chart, `U` corresponds
to an open set `U' ⊆ ℝ^N`, which by `euclid_open_monotone_finiteUnions_convex` is an increasing union
`⋃ W_k` of finite unions of convex open sets; each `W_k` is a finite union of convex coordinate
pieces, hence `Good`, and `Work.Cohomology.pd_good_iUnion` concludes.

This is the form in which the duality statement is glued along a finite coordinate cover of a
compact manifold.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **`Good` for an open subset of a coordinate ball.** -/
theorem pd_good_open_subset_chartBall {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    (∀ {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V)),
        Good N c U hU → Good N c V hV → Good N c (U ∩ V) hI →
        Good N c (U ∪ V) (hU.union hV)) →
    Good N c (∅ : Set M) isOpen_empty →
    (U : Set M) → U ⊆ (e ⁻¹' Metric.ball (e cc) (r / 2)) ∩ e.source → IsOpen U →
      ∀ (h : IsOpen U), Good N c U h := by
  intro e hball glue hempty U hUB hU hUproof
  set U' : Set (EuclideanSpace ℝ (Fin N)) := e '' U with hU'def
  have hUsrc : U ⊆ e.source := fun x hx => (hUB hx).2
  have hU'open : IsOpen U' := e.isOpen_image_of_subset_source hU hUsrc
  have hU'ball : U' ⊆ Metric.ball (e cc) (r / 2) := by
    rintro v ⟨x, hx, rfl⟩
    exact (hUB hx).1
  have hUeq : U = (e ⁻¹' U') ∩ e.source := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx, rfl⟩, hUsrc hx⟩
    · rintro ⟨⟨y, hy, hyx⟩, hxs⟩
      have hyx' : y = x := e.toPartialEquiv.injOn (hUsrc hy) hxs hyx
      rw [← hyx']
      exact hy
  obtain ⟨W, hWmono, hWsub, hWcov, hWpieces⟩ :=
    euclid_open_monotone_finiteUnions_convex N U' hU'open
  have hWopen : ∀ k, IsOpen (W k) := by
    intro k
    obtain ⟨s, hs, hWs⟩ := hWpieces k
    rw [hWs]
    exact isOpen_iUnion (fun Q => isOpen_iUnion (fun hQ => (hs Q hQ).1))
  set V : ℕ → Set M := fun k => (e ⁻¹' (W k)) ∩ e.source with hVdef
  have hVopen : ∀ k, IsOpen (V k) := fun k => by
    show IsOpen ((e ⁻¹' (W k)) ∩ e.source)
    rw [Set.inter_comm]
    exact e.isOpen_inter_preimage (hWopen k)
  have hVmono : Monotone V := by
    intro k l hkl x hx
    simp only [hVdef] at hx ⊢
    exact ⟨hWmono hkl hx.1, hx.2⟩
  have hVcov : (⋃ k, V k) = U := by
    simp only [hVdef]
    rw [← Set.iUnion_inter, ← Set.preimage_iUnion, hWcov, hUeq]
  have hVgood : ∀ k, Good N c (V k) (hVopen k) := by
    intro k
    obtain ⟨s, hs, hWs⟩ := hWpieces k
    have hprops : ∀ Q ∈ s.toList, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r := by
      intro Q hQ
      have hQ' : Q ∈ s := Finset.mem_toList.mp hQ
      exact ⟨(hs Q hQ').1, (hs Q hQ').2.1,
        (hs Q hQ').2.2.trans (hU'ball.trans (Metric.ball_subset_ball (by linarith)))⟩
    have hg := pd_good_list_pieces c hc hN cc r hr hball glue hempty s.toList hprops
    have hVeq : V k = pdUnion e s.toList := by
      simp only [hVdef, hWs]
      rw [pdPiece_iUnion_inter, pdUnion_toList]
    exact good_of_set_eq hVeq.symm (isOpen_pdUnion e _ (fun Q hQ => (hprops Q hQ).1))
      (hVopen k) hg
  have hbig := pd_good_iUnion V hVopen hVmono hVgood
  exact good_of_set_eq hVcov (isOpen_iUnion hVopen) hUproof hbig

end

end Work.Cohomology
