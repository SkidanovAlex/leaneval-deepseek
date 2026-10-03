import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# Uniqueness of the petal containing the eventual orbit of a parabolic-basin point

Combinatorial core of the Horn-map petal bookkeeping in Shishikura's §5:  the petals `V i` are
pairwise disjoint and forward invariant under `f`, and every orbit in the parabolic basin is
eventually captured by `⋃ i, V i`.  Since the petals are forward invariant, once an orbit enters a
petal it stays there; two memberships can therefore be propagated (the later iterate) to a common
point lying in both petals, forcing the two indices to coincide by disjointness.
-/

namespace Work.Horn.Basins

/-- Forward invariance of a set under `f` propagates to every iterate of `f`. -/
lemma iterate_mem_of_mem {f : ℂ → ℂ} {V : Set ℂ} (hV : ∀ z ∈ V, f z ∈ V) (k : ℕ) :
    ∀ z ∈ V, f^[k] z ∈ V := by
  induction k with
  | zero => intro z hz; simpa using hz
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact hV _ (ih z hz)

/-- If two forward-invariant sets each contain a point of one and the same orbit, they meet. -/
lemma inter_nonempty_of_iterate_mem {f : ℂ → ℂ} {V W : Set ℂ}
    (hV : ∀ z ∈ V, f z ∈ V) (hW : ∀ z ∈ W, f z ∈ W)
    {z : ℂ} {n m : ℕ} (hn : f^[n] z ∈ V) (hm : f^[m] z ∈ W) :
    (V ∩ W).Nonempty := by
  rcases le_total n m with h | h
  · refine ⟨f^[m] z, ?_, hm⟩
    have hm' : m = (m - n) + n := (Nat.sub_add_cancel h).symm
    rw [hm', Function.iterate_add_apply]
    exact iterate_mem_of_mem hV (m - n) _ hn
  · refine ⟨f^[n] z, hn, ?_⟩
    have hn' : n = (n - m) + m := (Nat.sub_add_cancel h).symm
    rw [hn', Function.iterate_add_apply]
    exact iterate_mem_of_mem hW (n - m) _ hm

theorem existsUnique_petal_index {f : ℂ → ℂ} {D : Set ℂ} {q : ℕ} {V : Fin q → Set ℂ}
    (hVmap : ∀ i, ∀ z ∈ V i, f z ∈ V i)
    (hVdisj : ∀ i j : Fin q, i ≠ j → Disjoint (V i) (V j))
    (hVcapture : ∀ z ∈ MandelDim.ParabolicBasin f D, ∃ n : ℕ, f^[n] z ∈ ⋃ i, V i) :
    ∀ z ∈ MandelDim.ParabolicBasin f D, ∃! i : Fin q, ∃ n : ℕ, f^[n] z ∈ V i := by
  intro z hz
  obtain ⟨n, hn⟩ := hVcapture z hz
  rw [Set.mem_iUnion] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ⟨n, hi⟩, ?_⟩
  intro j hj
  obtain ⟨m, hm⟩ := hj
  by_contra hne
  obtain ⟨w, hw1, hw2⟩ :=
    inter_nonempty_of_iterate_mem (hVmap i) (hVmap j) hi hm
  exact (Set.disjoint_left.mp (hVdisj i j (fun h => hne h.symm))) hw1 hw2

end Work.Horn.Basins
