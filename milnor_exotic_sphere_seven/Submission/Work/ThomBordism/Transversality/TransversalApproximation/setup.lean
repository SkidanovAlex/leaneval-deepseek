import Mathlib
import Submission.Work.ThomBordism.Transversality.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Setup lemmas for the transversality homotopy theorem

Elementary, self-contained ingredients of the proof of
`Work.ThomBordism.Transversality.TransversalApproximation`.  See the module docstring of
`Submission/Work/ThomBordism/Transversality/TransversalApproximation/transversalApproximation.lean`
for the overall plan of the proof.
-/

open scoped Manifold ContDiff MeasureTheory
open Function Set Topology Manifold Filter MeasureTheory

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.TransversalApproximation

noncomputable section

/-- **A uniform smallness bound for a family of curves through a compact set.**

Let `K` be a compact subset of a topological space `X`, let `y : X → ℝ^k → E` be continuous and
suppose `y x 0 ∈ U` for all `x ∈ K`, with `U` open.  Then there is `δ > 0` such that
`y x t ∈ U` for all `x ∈ K` and all `‖t‖ < δ`.

This is the tube lemma which guarantees that the intermediate points of a finite composition of
vertical translations stay in their boxes as long as the total translation is small. -/
theorem exists_uniform_ball_of_isCompact {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {k : ℕ} {K : Set X} (hK : IsCompact K)
    {y : X → EuclideanSpace ℝ (Fin k) → E}
    (hy : Continuous fun p : X × EuclideanSpace ℝ (Fin k) => y p.1 p.2)
    {U : Set E} (hU : IsOpen U) (h0 : ∀ x ∈ K, y x 0 ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ < δ → y x t ∈ U := by
  classical
  have hW : IsOpen {p : X × EuclideanSpace ℝ (Fin k) | y p.1 p.2 ∈ U} := hU.preimage hy
  have hstep : ∀ x ∈ K, ∃ (V : Set X) (δ : ℝ), V ∈ 𝓝 x ∧ 0 < δ ∧
      ∀ x' ∈ V, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ < δ → y x' t ∈ U := by
    intro x hx
    have hmem : (x, (0 : EuclideanSpace ℝ (Fin k))) ∈
        {p : X × EuclideanSpace ℝ (Fin k) | y p.1 p.2 ∈ U} := h0 x hx
    have h1 : {p : X × EuclideanSpace ℝ (Fin k) | y p.1 p.2 ∈ U} ∈
        𝓝 (x, (0 : EuclideanSpace ℝ (Fin k))) := hW.mem_nhds hmem
    rw [nhds_prod_eq] at h1
    obtain ⟨V, hV, A, hA, hVA⟩ := Filter.mem_prod_iff.mp h1
    obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp hA
    refine ⟨V, δ, hV, hδ, ?_⟩
    intro x' hx' t ht
    refine hVA (Set.mk_mem_prod hx' (hδA ?_))
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  choose V δ hV hδpos hVδ using hstep
  obtain ⟨s, hcover⟩ := hK.elim_nhds_subcover' V (fun x hx => hV x hx)
  rcases s.eq_empty_or_nonempty with hs | hs
  · have hKempty : K = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hmem := hcover hx
      rw [hs] at hmem
      simp at hmem
    exact ⟨1, one_pos, fun x hx _ _ => absurd hx (by rw [hKempty]; exact notMem_empty x)⟩
  · refine ⟨s.inf' hs (fun w : K => δ (w : X) w.2), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro b hb
      exact hδpos (b : X) b.2
    · intro x hx t ht
      obtain ⟨w, hws, hxw⟩ := Set.mem_iUnion₂.mp (hcover hx)
      refine hVδ (w : X) w.2 x hxw t (lt_of_lt_of_le ht ?_)
      exact Finset.inf'_le (fun w : K => δ (w : X) w.2) hws

/-- **A uniform smallness bound for a family of curves through a compact set, local form.**

Same conclusion as `exists_uniform_ball_of_isCompact`, but the continuity of `(x,t) ↦ y x t` is only
required *at* the points `(x, 0)`, `x ∈ K`.  This is the form in which the construction of the
perturbed map uses the lemma: the intermediate maps of the composition are only known to be smooth
on the open set `M × {‖t‖ < ε}`. -/
theorem exists_uniform_ball_of_isCompact_of_continuousAt {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] {k : ℕ} {K : Set X} (hK : IsCompact K)
    {y : X → EuclideanSpace ℝ (Fin k) → E}
    (hy : ∀ x ∈ K, ContinuousAt (fun p : X × EuclideanSpace ℝ (Fin k) => y p.1 p.2) (x, 0))
    {U : Set E} (hU : IsOpen U) (h0 : ∀ x ∈ K, y x 0 ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ < δ → y x t ∈ U := by
  have hstep : ∀ x ∈ K, ∃ (V : Set X) (δ : ℝ), V ∈ 𝓝 x ∧ 0 < δ ∧
      ∀ x' ∈ V, ∀ t : EuclideanSpace ℝ (Fin k), ‖t‖ < δ → y x' t ∈ U := by
    intro x hx
    have hmem : y x 0 ∈ U := h0 x hx
    have h1 : {p : X × EuclideanSpace ℝ (Fin k) | y p.1 p.2 ∈ U} ∈
        𝓝 (x, (0 : EuclideanSpace ℝ (Fin k))) :=
      (hy x hx).preimage_mem_nhds (hU.mem_nhds hmem)
    rw [nhds_prod_eq] at h1
    obtain ⟨V, hV, A, hA, hVA⟩ := Filter.mem_prod_iff.mp h1
    obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp hA
    refine ⟨V, δ, hV, hδ, ?_⟩
    intro x' hx' t ht
    refine hVA (Set.mk_mem_prod hx' (hδA ?_))
    rwa [Metric.mem_ball, dist_eq_norm, sub_zero]
  choose V δ hV hδpos hVδ using hstep
  obtain ⟨s, hcover⟩ := hK.elim_nhds_subcover' V (fun x hx => hV x hx)
  rcases s.eq_empty_or_nonempty with hs | hs
  · have hKempty : K = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hmem := hcover hx
      rw [hs] at hmem
      simp at hmem
    exact ⟨1, one_pos, fun x hx _ _ => absurd hx (by rw [hKempty]; exact notMem_empty x)⟩
  · refine ⟨s.inf' hs (fun w : K => δ (w : X) w.2), ?_, ?_⟩
    · rw [Finset.lt_inf'_iff]
      intro b hb
      exact hδpos (b : X) b.2
    · intro x hx t ht
      obtain ⟨w, hws, hxw⟩ := Set.mem_iUnion₂.mp (hcover hx)
      refine hVδ (w : X) w.2 x hxw t (lt_of_lt_of_le ht ?_)
      exact Finset.inf'_le (fun w : K => δ (w : X) w.2) hws

/-- **The model space of a compact `T2` manifold is finite-dimensional.**  (Compactness gives
local compactness, and `FiniteDimensional.of_locallyCompact_manifold` finishes.)  This is the
hypothesis under which the chartwise Sard argument of item 3 of the plan runs: it makes every chart
expression a map on an open subset of a Euclidean space. -/
theorem finiteDimensional_model {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M] [T2Space M]
    [Nonempty M] : FiniteDimensional ℝ E :=
  FiniteDimensional.of_locallyCompact_manifold M I

end

end Work.ThomBordism.Transversality.TransversalApproximation
