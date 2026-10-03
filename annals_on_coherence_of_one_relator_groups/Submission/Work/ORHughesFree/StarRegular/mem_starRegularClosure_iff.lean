import Mathlib
import Submission.Work.ORHughesFree.StarRegular

namespace Work.ORHughesFree.StarRegular

open Work.ORHughesFree

/-- One step of the approximating chain of [JZLA20, Proposition 2.2]: `Rₙ ⊆ Rₙ₊₁`. -/
private theorem chain_le_succ_aux {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) (n : ℕ) :
    (starRegularChain R n : Set U) ⊆ (starRegularChain R (n + 1) : Set U) := by
  intro x hx
  exact subset_starSubringClosure _ (Or.inl hx)

/-- The approximating chain is increasing. -/
private theorem chain_mono_aux {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) {m n : ℕ}
    (h : m ≤ n) : (starRegularChain R m : Set U) ⊆ (starRegularChain R n : Set U) :=
  monotone_nat_of_le_succ (fun k => chain_le_succ_aux R k) h

/-- The ∗-regular closure of a ∗-subring is exactly the union of the approximating chain
`R₀ ⊆ R₁ ⊆ ⋯` of [JZLA20, Proposition 2.2].

The key point is that the union `⋃ₙ Rₙ` is already a ∗-subring: it is closed under `+`, `*`, `-`,
`star`, `0` and `1` because the chain is increasing and each `Rₙ` is a ∗-subring. Hence the
∗-subring it generates -- which is `starRegularClosure R` by definition -- is the union itself. -/
theorem mem_starRegularClosure_iff {U : Type*} [Ring U] [StarRing U] (R : StarSubring U) (x : U) :
    x ∈ (starRegularClosure R : Set U) ↔ ∃ n, x ∈ (starRegularChain R n : Set U) := by
  constructor
  · intro hx
    let S : Set U := ⋃ n, (starRegularChain R n : Set U)
    have hx' : x ∈ Subring.closure (S ∪ star '' S) := hx
    -- `S` is already closed under all the ∗-ring operations.
    have key : x ∈ S := by
      refine Subring.closure_induction (p := fun y _ => y ∈ S) ?_ ?_ ?_ ?_ ?_ ?_ hx'
      · -- generators of the ∗-subring closure
        rintro y (hy | ⟨z, hz, rfl⟩)
        · exact hy
        · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨n, (starRegularChain R n).star_mem' hn⟩
      · exact Set.mem_iUnion.mpr ⟨0, Subring.zero_mem _⟩
      · exact Set.mem_iUnion.mpr ⟨0, Subring.one_mem _⟩
      · -- addition
        rintro y z _ _ hy hz
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨max m n, Subring.add_mem _
          (chain_mono_aux R (le_max_left m n) hm) (chain_mono_aux R (le_max_right m n) hn)⟩
      · -- negation
        rintro y _ hy
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion.mpr ⟨m, Subring.neg_mem _ hm⟩
      · -- multiplication
        rintro y z _ _ hy hz
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hy
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨max m n, Subring.mul_mem _
          (chain_mono_aux R (le_max_left m n) hm) (chain_mono_aux R (le_max_right m n) hn)⟩
    exact Set.mem_iUnion.mp key
  · -- every element of the chain lies in the ∗-subring it generates
    rintro ⟨n, hn⟩
    exact subset_starSubringClosure _ (Set.mem_iUnion.mpr ⟨n, hn⟩)

end Work.ORHughesFree.StarRegular
