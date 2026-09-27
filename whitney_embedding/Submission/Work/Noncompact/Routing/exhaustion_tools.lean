import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# Two elementary tools for the line construction

* `exists_avoid_level`: a compact set is contained in a level of a monotone exhaustion of the space
  (this is the private `exists_subset_of_mono_exhaust` of `Routing/exists_canals.lean`, made public;
  it is what turns "the piece at level `j` lies in `(K j)ᶜ`" into the `hdeep` hypothesis of
  `rayAssembly_of_pieces`);
* `not_isCompact_closure_of_cofinal`: the cofinality hypothesis of
  `Work.Noncompact.Routing.exists_smoothProperLine` implies `¬ IsCompact (closure W)`, hence (with
  `ProperLine`/`CompressionTube` machinery) that `W` admits a pocket-free exhaustion.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- **Every compact set is contained in a level of a monotone exhaustion.** -/
theorem exists_avoid_level {M : Type*} [TopologicalSpace M] {K : ℕ → Set M}
    (hKmono : ∀ i, K i ⊆ K (i + 1)) (hKint : ∀ i, K i ⊆ interior (K (i + 1)))
    (hKu : (⋃ i, K i) = (Set.univ : Set M)) {C : Set M} (hC : IsCompact C) :
    ∃ I, C ⊆ K I := by
  have hopen : C ⊆ ⋃ i, interior (K (i + 1)) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, K i by rw [hKu]; trivial)
    exact Set.mem_iUnion.mpr ⟨i, hKint i hi⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun i : ℕ => interior (K (i + 1)))
    (fun i => isOpen_interior) hopen
  have hmono : Monotone K := monotone_nat_of_le_succ hKmono
  refine ⟨t.sup (fun i => i + 1), fun x hx => ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  have hle : i + 1 ≤ t.sup (fun j => j + 1) := Finset.le_sup (f := fun j => j + 1) hit
  exact hmono hle (interior_subset hxi)

/-- **Cofinality implies non-compact closure.** -/
theorem not_isCompact_closure_of_cofinal {M : Type*} [TopologicalSpace M] {W : Set M}
    (hcof : ∀ C : Set M, IsCompact C → ∃ x ∈ W, x ∉ C ∧
      ¬ IsCompact (closure (connectedComponentIn (W \ C) x))) :
    ¬ IsCompact (closure W) := by
  intro hcomp
  obtain ⟨x, hxW, hx, -⟩ := hcof (closure W) hcomp
  exact hx (subset_closure hxW)

end Work.Noncompact.Routing
