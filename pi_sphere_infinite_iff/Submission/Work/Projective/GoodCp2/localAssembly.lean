import Mathlib
import Submission.Work.Projective.GoodCp2.fork.chart_relCohomology_vanishing_of_compact
import Submission.Work.Projective.GoodCp2.fork.pd_good_univ
import Submission.Work.Projective.GoodCp2.fork.pd_good_open_subset_chartBall
import Submission.Work.Projective.GoodCp2.fork.pd_good_list_pieces
import Submission.Work.Projective.GoodCp2.glue

set_option synthInstance.maxHeartbeats 400000

/-!
# The `Good`-assembly for a compact charted manifold, with a chart-local gluing step

`Work.Cohomology.pd_good_univ` assembles `Good N c Set.univ` for a compact charted `N`-manifold
from a gluing step `glue : Good U → Good V → Good (U∩V) → Good (U∪V)`, taken as a hypothesis
(generic in `U`, `V`).  The proof only ever applies `glue` to pairs whose intersection
`U ∩ V` lies inside a *single* chart: `pd_good_list_pieces` glues two unions of convex pieces of one
chart, and `pd_good_univ` glues a coordinate ball with a finite union of coordinate balls.

Here we re-run the same assembly with the gluing step *specialised* to that situation, so that its
only supplementary input is the high-degree vanishing of the compactly supported cohomology of an
open subset of a chart, which is available in the workspace in the clean form
`Work.Cohomology.chart_relCohomology_vanishing_of_compact`:

`glue_chart c₀ hUV : Good U → Good V → Good (U∩V) → Good (U∪V)`, for `U ∩ V ⊆ (chartAt c₀).source`.

Thus `pd_good_univ_local : Good N c Set.univ` rests only on inputs free of unsound axioms.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.Projective

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Work.Cohomology

noncomputable section

/-! ## The chart-local gluing step -/

/-- **The gluing step of `Good`, for an intersection contained in a single chart.**  If
`U ∩ V ⊆ (chartAt c₀).source` then the two-cover gluing holds, by `glue_of_vanishing` with the
high-degree vanishing of compactly supported cohomology supplied by
`Work.Cohomology.chart_relCohomology_vanishing_of_compact`. -/
theorem glue_chart {M : TopCat} [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    {c : (singularChains ℤ M).homology N}
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V) (hI : IsOpen (U ∩ V))
    (hUU : Good N c U hU) (hVV : Good N c V hV) (hII : Good N c (U ∩ V) hI)
    (c₀ : M) (hUV : U ∩ V ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) c₀).source) :
    Good N c (U ∪ V) (hU.union hV) :=
  glue_of_vanishing hU hV hI hUU hVV hII
    (fun k hk K hK hKc =>
      chart_relCohomology_vanishing_of_compact c₀ (U ∩ V) hUV hI k hk K hK hKc)

/-! ## `Good` for finite unions of convex pieces of one chart -/

/-- **`Good` for a finite union of convex coordinate pieces**, with the chart-local gluing step. -/
theorem pd_good_list_pieces_local {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    Good N c (∅ : Set M) isOpen_empty →
    (l : List (Set (EuclideanSpace ℝ (Fin N)))) →
    (hl : ∀ Q ∈ l, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r) →
    Good N c (pdUnion e l) (isOpen_pdUnion e l (fun Q hQ => (hl Q hQ).1)) := by
  intro e hball hempty
  have main : ∀ (n : ℕ) (l : List (Set (EuclideanSpace ℝ (Fin N)))), l.length = n →
      (hl : ∀ Q ∈ l, IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r) →
      Good N c (pdUnion e l) (isOpen_pdUnion e l (fun Q hQ => (hl Q hQ).1)) := by
    intro n
    induction n with
    | zero =>
        intro l hlen hl
        have hl_nil : l = [] := List.eq_nil_of_length_eq_zero hlen
        subst hl_nil
        exact good_of_open_eq _ _ hempty
    | succ n ih =>
        intro l hlen hl
        cases l with
        | nil => exact good_of_open_eq _ _ hempty
        | cons a t =>
            have htlen : t.length = n := by
              simp only [List.length_cons] at hlen
              omega
            have haopen : IsOpen (pdPiece e a) :=
              isOpen_pdPiece e (hl a List.mem_cons_self).1
            have htopen : IsOpen (pdUnion e t) :=
              isOpen_pdUnion e t (fun Q hQ => (hl Q (List.mem_cons_of_mem _ hQ)).1)
            have himg : ∀ Q ∈ t.map (fun Q => Q ∩ a),
                IsOpen Q ∧ Convex ℝ Q ∧ Q ⊆ Metric.ball (e cc) r := by
              intro Q hQ
              obtain ⟨Q₀, hQ₀, rfl⟩ := List.mem_map.mp hQ
              have h1 := hl Q₀ (List.mem_cons_of_mem _ hQ₀)
              have h2 := hl a List.mem_cons_self
              exact ⟨h1.1.inter h2.1, h1.2.1.inter h2.2.1,
                Set.inter_subset_right.trans h2.2.2⟩
            have hmapgood : Good N c (pdUnion e (t.map (fun Q => Q ∩ a)))
                (isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1)) :=
              ih (t.map (fun Q => Q ∩ a)) (by rw [List.length_map, htlen]) himg
            have hIopen : IsOpen (pdPiece e a ∩ pdUnion e t) := by
              rw [pdPiece_inter_pdUnion]
              exact isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1)
            have hUV : pdPiece e a ∩ pdUnion e t ⊆
                (chartAt (EuclideanSpace ℝ (Fin N)) cc).source := by
              intro y hy
              rw [show (chartAt (EuclideanSpace ℝ (Fin N)) cc).source = e.source from rfl]
              exact (Set.inter_subset_left hy).2
            have hgood : Good N c (pdPiece e a ∪ pdUnion e t) (haopen.union htopen) :=
              glue_chart haopen htopen hIopen
                (good_piece c hc hN cc r hr hball hempty a (hl a List.mem_cons_self).1
                  (hl a List.mem_cons_self).2.1 (hl a List.mem_cons_self).2.2)
                (good_of_open_eq _ _
                  (ih t htlen (fun Q hQ => hl Q (List.mem_cons_of_mem _ hQ))))
                (good_of_set_eq (pdPiece_inter_pdUnion e a t).symm
                  (isOpen_pdUnion e _ (fun Q hQ => (himg Q hQ).1))
                  (haopen.inter htopen) hmapgood)
                cc hUV
            exact good_of_open_eq _ _ hgood
  intro l hl
  exact main l.length l rfl hl

/-! ## `Good` for an open subset of a coordinate ball -/

/-- **`Good` for an open subset of a coordinate ball**, with the chart-local gluing step. -/
theorem pd_good_open_subset_chartBall_local {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N) (cc : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ cc
    Metric.ball (e cc) r ⊆ e.target →
    Good N c (∅ : Set M) isOpen_empty →
    (U : Set M) → U ⊆ (e ⁻¹' Metric.ball (e cc) (r / 2)) ∩ e.source → IsOpen U →
      ∀ (h : IsOpen U), Good N c U h := by
  intro e hball hempty U hUB hU hUproof
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
    have hg := pd_good_list_pieces_local c hc hN cc r hr hball hempty s.toList hprops
    have hVeq : V k = pdUnion e s.toList := by
      simp only [hVdef, hWs]
      rw [pdPiece_iUnion_inter, pdUnion_toList]
    exact good_of_set_eq hVeq.symm (isOpen_pdUnion e _ (fun Q hQ => (hprops Q hQ).1))
      (hVopen k) hg
  have hbig := pd_good_iUnion V hVopen hVmono hVgood
  exact good_of_set_eq hVcov (isOpen_iUnion hVopen) hUproof hbig

/-! ## `Good` for the whole compact manifold -/

/-- **`Good N c Set.univ` for a compact charted `N`-manifold**, from the chart-local gluing step
and the fundamental-class condition `hc`. -/
theorem pd_good_univ_local {M : TopCat} [CompactSpace M] [T2Space M] {N : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M]
    (c : (singularChains ℤ M).homology N)
    (hc : ∀ x : M, Submodule.span ℤ
      {((HomologicalComplex.homologyMap
          (CategoryTheory.Limits.cokernel.π (inclChains M {y | y ≠ x})) N) c)} = ⊤)
    (hN : 1 ≤ N)
    (hempty : Good N c (∅ : Set M) isOpen_empty) :
    Good N c (Set.univ : Set M) isOpen_univ := by
  classical
  have hrad : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) x) x) r
        ⊆ (chartAt (EuclideanSpace ℝ (Fin N)) x).target := by
    intro x
    exact Metric.mem_nhds_iff.mp
      (((chartAt (EuclideanSpace ℝ (Fin N)) x).open_target).mem_nhds
        ((chartAt (EuclideanSpace ℝ (Fin N)) x).map_source (mem_chart_source _ x)))
  choose ρ hρpos hρsub using hrad
  let B : M → Set M := fun z =>
    ((chartAt (EuclideanSpace ℝ (Fin N)) z) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) z).source
  have hBopen : ∀ z, IsOpen (B z) := fun z => by
    show IsOpen (((chartAt (EuclideanSpace ℝ (Fin N)) z) ⁻¹'
        Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      ∩ (chartAt (EuclideanSpace ℝ (Fin N)) z).source)
    rw [Set.inter_comm]
    exact (chartAt (EuclideanSpace ℝ (Fin N)) z).isOpen_inter_preimage Metric.isOpen_ball
  have hBself : ∀ z, z ∈ B z := fun z => by
    constructor
    · exact Metric.mem_ball_self (half_pos (hρpos z))
    · exact mem_chart_source _ z
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBopen
    (fun z _ => Set.mem_iUnion.mpr ⟨z, hBself z⟩)
  have hBgood : ∀ z : M, Good N c (B z) (hBopen z) := by
    intro z
    have h := good_piece c hc hN z (ρ z) (hρpos z) (hρsub z) hempty
      (Metric.ball ((chartAt (EuclideanSpace ℝ (Fin N)) z) z) (ρ z / 2))
      Metric.isOpen_ball (convex_ball _ _)
      (Metric.ball_subset_ball (half_le_self (le_of_lt (hρpos z))))
    exact good_of_open_eq _ _ h
  have main : ∀ u : Finset M, Good N c (covUnion B u) (isOpen_covUnion hBopen u) := by
    intro u
    induction u using Finset.induction with
    | empty =>
        have hEq : covUnion B (∅ : Finset M) = (∅ : Set M) := by
          simp only [covUnion, Finset.coe_empty, Set.image_empty, Set.sUnion_empty]
        exact good_of_set_eq hEq.symm isOpen_empty (isOpen_covUnion hBopen ∅) hempty
    | insert z u hz ih =>
        have hzopen : IsOpen (B z) := hBopen z
        have huopen : IsOpen (covUnion B u) := isOpen_covUnion hBopen u
        have hIopen : IsOpen (covUnion B u ∩ B z) := huopen.inter hzopen
        have hI'open : IsOpen (B z ∩ covUnion B u) := hzopen.inter huopen
        have hinter : Good N c (covUnion B u ∩ B z) hIopen := by
          have h := pd_good_open_subset_chartBall_local c hc hN z (ρ z) (hρpos z)
            (hρsub z) hempty (covUnion B u ∩ B z) ?_ hIopen hIopen
          · exact h
          · rintro y ⟨-, hy⟩
            exact hy
        have hgood : Good N c (B z ∪ covUnion B u) (hzopen.union huopen) :=
          glue_chart hzopen huopen hI'open
            (good_of_open_eq _ _ (hBgood z))
            (good_of_open_eq _ _ ih)
            (good_of_set_eq (Set.inter_comm _ _) hIopen hI'open hinter)
            z (by
              intro y hy
              exact (Set.inter_subset_left hy).2)
        exact good_of_set_eq (covUnion_insert B z u).symm (hzopen.union huopen)
          (isOpen_covUnion hBopen (insert z u)) hgood
  have hcov : covUnion B t = (Set.univ : Set M) := by
    refine Set.eq_univ_iff_forall.mpr (fun x => ?_)
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨z, hzt, hxz⟩ := hx
    exact Set.mem_sUnion.mpr
      ⟨B z, (Set.mem_image B ((t : Set M)) (B z)).mpr ⟨z, by simpa using hzt, rfl⟩, hxz⟩
  exact good_of_set_eq hcov (isOpen_covUnion hBopen t) isOpen_univ (main t)

end

end Work.Projective
