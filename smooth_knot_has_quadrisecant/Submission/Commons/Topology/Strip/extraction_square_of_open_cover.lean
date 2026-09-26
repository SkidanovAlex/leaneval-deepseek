import Mathlib
import Submission.Commons.Topology.Strip.barrier_bottom_top_of_no_left_right

/-!
# The extraction square: the point-set core of the two-set van Kampen / Mayer–Vietoris relation

Let `Ω₁, Ω₂ ⊆ ℝ × ℝ` be open.  Let `F : ℝ × ℝ → ℝ × ℝ` be continuous and assume that on the unit
square `sq = [0,1] × [0,1]` its image is covered by `Ω₁ ∪ Ω₂`, that the bottom edge lands in `Ω₁`
and the top edge lands in `Ω₂`.  Then there is a path inside the square from the left edge
`{x = 0}` to the right edge `{x = 1}` whose image under `F` lies entirely in `Ω₁ ∩ Ω₂`.

This is the "extraction" step: from a *filling* of a loop by two open sets one extracts a
connection in the intersection.  It is the point-set heart of the exactness of
`H₁(Ω₁∩Ω₂) → H₁(Ω₁) ⊕ H₁(Ω₂) → H₁(Ω₁∪Ω₂)` at the middle term (equivalently of the two-set van
Kampen theorem), in the elementary form "two loops, one in `Ω₁` and one in `Ω₂`, that are homotopic
in `Ω₁ ∪ Ω₂`, admit a common lift in `Ω₁ ∩ Ω₂`".

The proof is the standard planar duality: if no left–right path stays in `Ω₁ ∩ Ω₂`, the complement
of `Ω₁ ∩ Ω₂` inside the square meets every left–right path, so by the commons lemma
`barrier_bottom_top_of_no_left_right` it contains a preconnected set `C` meeting the bottom and the
top edge of the square; a preconnected set inside the disjoint closed union `Ω₁ᶜ ∪ Ω₂ᶜ` lies in one
of the two claws, contradicting `bottom ⊆ Ω₁` or `top ⊆ Ω₂`.
-/

open Set

namespace Commons.Topology.Strip

/-- The unit square. -/
def sq : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

theorem sq_eq_rect : sq = {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} := by
  ext q; simp only [sq, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]; tauto

theorem isClosed_sq : IsClosed sq := by
  rw [sq]; exact isClosed_Icc.prod isClosed_Icc

/-- **The extraction square (map form).**

For open `Ω₁, Ω₂ ⊆ ℝ × ℝ`, a continuous `F`, with the square's image covered by `Ω₁ ∪ Ω₂`, the
bottom edge in `Ω₁` and the top edge in `Ω₂`, there is a path inside the square from the left edge
to the right edge whose image lies in `Ω₁ ∩ Ω₂`. -/
theorem extraction_square_map {Ω₁ Ω₂ : Set (ℝ × ℝ)} (h₁ : IsOpen Ω₁) (h₂ : IsOpen Ω₂)
    {F : C(ℝ × ℝ, ℝ × ℝ)}
    (hcov : ∀ q : ℝ × ℝ, q ∈ sq → F q ∈ Ω₁ ∪ Ω₂)
    (hbot : ∀ q : ℝ × ℝ, q ∈ sq → q.2 = 0 → F q ∈ Ω₁)
    (htop : ∀ q : ℝ × ℝ, q ∈ sq → q.2 = 1 → F q ∈ Ω₂) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ sq) ∧ (γ 0).1 = 0 ∧ (γ 1).1 = 1 ∧
        (∀ t, F (γ t) ∈ Ω₁ ∩ Ω₂) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `K` is the part of the square forced to stay outside `Ω₁ ∩ Ω₂`.
  set K : Set (ℝ × ℝ) := sq ∩ F ⁻¹' (Ω₁ ∩ Ω₂)ᶜ with hKdef
  have hKcl : IsClosed K :=
    isClosed_sq.inter (IsClosed.preimage F.continuous (h₁.inter h₂).isClosed_compl)
  have hKsub : K ⊆ {q : ℝ × ℝ | 0 ≤ q.1 ∧ q.1 ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ 1} := by
    rw [hKdef]; rintro q ⟨hq, -⟩; rw [sq_eq_rect] at hq; exact hq
  obtain ⟨C, hCK, hCpc, hCb, hCt⟩ :=
    barrier_bottom_top_of_no_left_right (p := 1) (a := 0) (b := 1) (by norm_num) (by norm_num)
      hKsub hKcl (fun γ hγrect hγ0 hγ1 hγK => by
        obtain ⟨t, ht⟩ := hcon γ (fun t => by rw [sq_eq_rect]; exact hγrect t) hγ0 hγ1
        exact hγK t (by
          rw [hKdef, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
          exact ⟨by rw [sq_eq_rect]; exact hγrect t, ht⟩))
  set D₁ : Set (ℝ × ℝ) := sq ∩ F ⁻¹' (Ω₁ᶜ) with hD₁
  set D₂ : Set (ℝ × ℝ) := sq ∩ F ⁻¹' (Ω₂ᶜ) with hD₂
  have hD₁cl : IsClosed D₁ := isClosed_sq.inter (IsClosed.preimage F.continuous h₁.isClosed_compl)
  have hD₂cl : IsClosed D₂ := isClosed_sq.inter (IsClosed.preimage F.continuous h₂.isClosed_compl)
  have hCD : C ⊆ D₁ ∪ D₂ := by
    intro q hq
    have hqK : q ∈ sq ∩ F ⁻¹' (Ω₁ ∩ Ω₂)ᶜ := hCK hq
    obtain ⟨hqsq, hqK⟩ := hqK
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff] at hqK
    by_cases h : F q ∈ Ω₁
    · exact Or.inr ⟨hqsq, fun h2 => hqK ⟨h, h2⟩⟩
    · exact Or.inl ⟨hqsq, h⟩
  have hdisj : C ∩ (D₁ ∩ D₂) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro q ⟨hqC, hq1, hq2⟩
    have hmem1 : ¬ (F q ∈ Ω₁) := by
      have := hq1.2; rwa [Set.mem_preimage, Set.mem_compl_iff] at this
    have hmem2 : ¬ (F q ∈ Ω₂) := by
      have := hq2.2; rwa [Set.mem_preimage, Set.mem_compl_iff] at this
    rcases hcov q (hCK hqC).1 with h | h
    · exact hmem1 h
    · exact hmem2 h
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hCpc D₁ D₂ hD₁cl hD₂cl hCD hdisj
    with hC1 | hC2
  · obtain ⟨q, hqC, hqb⟩ := hCb
    have h1 : q ∈ D₁ := hC1 hqC
    have h1' : ¬ (F q ∈ Ω₁) := by
      have := h1.2; rwa [Set.mem_preimage, Set.mem_compl_iff] at this
    exact h1' (hbot q (hCK hqC).1 hqb)
  · obtain ⟨q, hqC, hqt⟩ := hCt
    have h2 : q ∈ D₂ := hC2 hqC
    have h2' : ¬ (F q ∈ Ω₂) := by
      have := h2.2; rwa [Set.mem_preimage, Set.mem_compl_iff] at this
    exact h2' (htop q (hCK hqC).1 hqt)

/-- **The extraction square (identity form).**  The special case `F = id`. -/
theorem extraction_square {Ω₁ Ω₂ : Set (ℝ × ℝ)} (h₁ : IsOpen Ω₁) (h₂ : IsOpen Ω₂)
    (hcov : sq ⊆ Ω₁ ∪ Ω₂) (hbot : {q : ℝ × ℝ | q.2 = 0} ⊆ Ω₁)
    (htop : {q : ℝ × ℝ | q.2 = 1} ⊆ Ω₂) :
    ∃ γ : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ),
      (∀ t, γ t ∈ sq) ∧ (γ 0).1 = 0 ∧ (γ 1).1 = 1 ∧ (∀ t, γ t ∈ Ω₁ ∩ Ω₂) := by
  obtain ⟨γ, h1, h2, h3, h4⟩ :=
    extraction_square_map h₁ h₂ (F := ContinuousMap.id (ℝ × ℝ))
      (fun q hq => hcov hq) (fun q _ h => hbot h) (fun q _ h => htop h)
  exact ⟨γ, h1, h2, h3, h4⟩

end Commons.Topology.Strip
