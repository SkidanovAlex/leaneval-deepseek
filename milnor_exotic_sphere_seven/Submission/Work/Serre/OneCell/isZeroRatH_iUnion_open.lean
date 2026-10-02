import Mathlib
import Submission.Work.Serre.OneCell.Prelim

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Vanishing of rational homology over a pairwise disjoint open union

If `o : κ → Set Z` is a family of pairwise disjoint open subsets of `Z` and each piece `o i` has
vanishing rational homology in degree `k`, then the union `⋃ i, o i` has vanishing rational
homology in degree `k`.

The proof is the standard one: because the pieces are pairwise disjoint and open, the union is the
disjoint union (topological sum) of the pieces — the canonical map
`Σ i, ↥(o i) → ↥(⋃ i, o i)` is a homeomorphism.  Rational homology of a disjoint union is the
direct sum of the rational homologies of the pieces
(`Work.Serre.OneCell.isZero_homology_sigma`, built on the coproduct decomposition of the singular
chain complex), so the vanishing transfers.
-/

namespace Work.Serre.OneCell

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- Two subtype elements with the same underlying point living over equal indices are `HEq`. -/
theorem heq_subtype_of_eq {Z : Type} {κ : Type} (o : κ → Set Z) :
    ∀ {a b : κ} (_ : a = b) {x : Z} (ha : x ∈ o a) (hb : x ∈ o b),
      HEq (⟨x, ha⟩ : ↥(o a)) (⟨x, hb⟩ : ↥(o b)) := by
  intro a b h x ha hb
  subst h
  exact heq_of_eq (Subtype.ext rfl)

/-- **A pairwise disjoint family of open sets is the topological sum of its members.**  The
canonical map `Σ i, ↥(o i) → ↥(⋃ i, o i)` is a homeomorphism. -/
theorem homeo_iUnion_sigma {Z : Type} [TopologicalSpace Z] {κ : Type} (o : κ → Set Z)
    (hopen : ∀ i, IsOpen (o i)) (hdisj : Pairwise fun i j => Disjoint (o i) (o j)) :
    Nonempty (↥(⋃ i, o i) ≃ₜ (Σ i, ↥(o i))) := by
  classical
  -- the trace of `o i` on the union: the points of the union lying in the `i`-th piece
  let P : κ → Set ↥(⋃ i, o i) := fun i => {z | (z : Z) ∈ o i}
  -- the forward map: `(i, x) ↦ x`
  let f : (Σ i, ↥(o i)) → ↥(⋃ i, o i) :=
    fun x => ⟨x.2.1, Set.mem_iUnion.mpr ⟨x.1, x.2.2⟩⟩
  -- the backward map: a point goes to its (unique) index and itself
  let g : ↥(⋃ i, o i) → (Σ i, ↥(o i)) := fun z =>
    ⟨Classical.choose (Set.mem_iUnion.mp z.2),
      ⟨z.1, Classical.choose_spec (Set.mem_iUnion.mp z.2)⟩⟩
  -- the two maps are inverse to each other
  have hfg : Function.LeftInverse g f := by
    intro x
    obtain ⟨i, a⟩ := x
    show g (f ⟨i, a⟩) = ⟨i, a⟩
    have hc : Classical.choose (Set.mem_iUnion.mp (f ⟨i, a⟩).2) = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj hne)
        (Classical.choose_spec (Set.mem_iUnion.mp (f ⟨i, a⟩).2)) a.2
    exact Sigma.ext hc (heq_subtype_of_eq o hc _ _)
  have hgf : Function.RightInverse g f := by
    intro z
    exact Subtype.ext rfl
  -- the forward map is continuous
  have hfcont : Continuous f :=
    (continuous_sigma (fun i => continuous_subtype_val)).subtype_mk _
  -- the backward map is continuous: on each open piece it is an inclusion into a summand
  have hgcont : Continuous g := by
    refine continuous_of_cover_nhds (s := P) (fun z => ?_) (fun i => ?_)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp z.2
      exact ⟨i, ((hopen i).preimage continuous_subtype_val).mem_nhds hi⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have hkey : ∀ z : ↥(P i),
          g z.1 = (⟨i, (⟨z.1.1, z.2⟩ : ↥(o i))⟩ : Σ j, ↥(o j)) := by
        intro z
        have hc : Classical.choose (Set.mem_iUnion.mp z.1.2) = i := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne)
            (Classical.choose_spec (Set.mem_iUnion.mp z.1.2)) z.2
        exact Sigma.ext hc (heq_subtype_of_eq o hc _ _)
      have hcont : Continuous (fun z : ↥(P i) =>
          (⟨i, (⟨z.1.1, z.2⟩ : ↥(o i))⟩ : Σ j, ↥(o j))) :=
        (continuous_sigmaMk (i := i)).comp
          ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
      exact hcont.congr (fun z => (hkey z).symm)
  exact ⟨{ toFun := g, invFun := f, left_inv := hgf, right_inv := hfg,
            continuous_toFun := hgcont, continuous_invFun := hfcont }⟩

/-- **Vanishing of rational homology over a pairwise disjoint open union.**  If every piece `o i`
has `H_k(o i; ℚ) = 0`, then `H_k(⋃ i, o i; ℚ) = 0`. -/
theorem isZeroRatH_iUnion_open {Z : Type} [TopologicalSpace Z] {κ : Type} (o : κ → Set Z)
    (hopen : ∀ i, IsOpen (o i)) (hdisj : Pairwise fun i j => Disjoint (o i) (o j)) (k : ℕ)
    (h : ∀ i, CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of ↥(o i)) k)) :
    CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of ↥(⋃ i, o i)) k) := by
  classical
  obtain ⟨e⟩ := homeo_iUnion_sigma o hopen hdisj
  exact isZero_ratH_of_homeo e k (isZero_homology_sigma (fun i => ↥(o i)) k h)

end

end Work.Serre.OneCell
