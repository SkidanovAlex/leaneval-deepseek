import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology
open Set Function

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
/-- A flow box of time `ε` for a vector field is also a flow box of any smaller time `ε' ≤ ε`. -/
theorem IsFlowBox.mono {v : (x : M) → TangentSpace (𝓡 n) x} {ε ε' : ℝ} {U : Set M}
    {Ψ : ℝ → M → M} (h : IsFlowBox v ε U Ψ) (hε : ε' ≤ ε) : IsFlowBox v ε' U Ψ := by
  have hsub : Set.Ioo (-ε') ε' ⊆ Set.Ioo (-ε) ε := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨h.1.mono (Set.prod_mono hsub Subset.rfl), fun x hx => ⟨(h.2 x hx).1, ?_⟩⟩
  exact ((h.2 x hx).2).mono hsub

/-- On a compact manifold, local flow boxes can be taken with a uniform time `ε > 0`: there is a
single `ε > 0` such that every point admits an integral curve defined on `Ioo (-ε) ε`, and every
point lies in a flow box of time `ε`. -/
theorem flow_box_uniform {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    {v : (x : M) → TangentSpace (𝓡 n) x}
    (hbox : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > 0, ∃ Ψ : ℝ → M → M, IsFlowBox v ε U Ψ) :
    ∃ ε > 0,
      (∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Set.Ioo (-ε) ε)) ∧
      (∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ Ψ : ℝ → M → M, IsFlowBox v ε U Ψ) := by
  classical
  rcases isEmpty_or_nonempty M with hempty | hne
  · exact ⟨1, one_pos, fun x => (hempty.false x).elim, fun p => (hempty.false p).elim⟩
  let p₀ : M := Classical.choice hne
  -- Pick a flow box at every point.
  choose U hU using hbox
  choose ε hε using fun p => (hU p).2.2
  choose Ψ hΨ using fun p => (hε p).2
  -- The boxes cover `M`; extract a finite subcover.
  have hcover : (Set.univ : Set M) ⊆ ⋃ p, U p :=
    fun x _ => Set.mem_iUnion.2 ⟨x, (hU x).2.1⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun p => (hU p).1) hcover
  have htne : t.Nonempty := by
    obtain ⟨q, hq, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p₀))
    exact ⟨q, hq⟩
  -- The uniform time is the minimum of the times of the finitely many boxes.
  have hsne : (t.image ε).Nonempty := htne.image ε
  have hminpos : 0 < (t.image ε).min' hsne := by
    obtain ⟨q, -, hqε⟩ := Finset.mem_image.1 (Finset.min'_mem (t.image ε) hsne)
    rw [← hqε]
    exact (hε q).1
  have hminle : ∀ q ∈ t, (t.image ε).min' hsne ≤ ε q := fun q hq =>
    (Finset.isLeast_min' (t.image ε) hsne).2 (Finset.mem_image_of_mem ε hq)
  have coord : ∀ p : M, ∃ q ∈ t, p ∈ U q := by
    intro p
    obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ p))
    exact ⟨q, hq, hxq⟩
  refine ⟨(t.image ε).min' hsne, hminpos, fun x => ?_, fun p => ?_⟩
  · obtain ⟨q, hq, hxq⟩ := coord x
    exact ⟨fun t => Ψ q t x, ((hΨ q).2 x hxq).1,
      ((hΨ q).2 x hxq).2.mono
        (fun t ht => ⟨by linarith [ht.1, hminle q hq], by linarith [ht.2, hminle q hq]⟩)⟩
  · obtain ⟨q, hq, hpq⟩ := coord p
    exact ⟨U q, (hU q).1, hpq, Ψ q, (hΨ q).mono (hminle q hq)⟩

end Work.Morse
