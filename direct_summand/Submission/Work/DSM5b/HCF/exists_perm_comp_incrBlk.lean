import Mathlib
import Submission.Work.DSM5b.HCF.BlkDefs

universe u

namespace Work.DSM5b.HCF

/-- **Every block tuple is a permutation of the increasing enumeration.**

For a finset `S₀` with `S₀.card = k' + 1`, both a tuple `σ` with `tupRng σ = S₀` and the increasing
enumeration `incrBlk S₀ k' hcard` are bijections `Fin (k' + 1) → S₀`; hence `σ.1` is the
increasing enumeration composed with a permutation of the positions.

The proof composes the two bijections: since `incrBlk` is strictly increasing, it is injective, so
for every position `i` there is a (unique) position `j` with `incrBlk j = σ i`; this assignment is a
permutation of `Fin (k' + 1)` and by construction `σ = incrBlk ∘ π`. -/
theorem exists_perm_comp_incrBlk {ι : Type u} [DecidableEq ι] [LinearOrder ι] {k' : ℕ}
    (S₀ : Finset ι) (hcard : k' + 1 = S₀.card) (σ : Work.DSM5b.HCF.BlkIdx S₀ k') :
    ∃ π : Equiv.Perm (Fin (k' + 1)), σ.1 = (Work.DSM5b.HCF.incrBlk S₀ k' hcard).1 ∘ π := by
  classical
  obtain ⟨g0, hg0⟩ := σ
  let f : Fin (k' + 1) → ι := (Work.DSM5b.HCF.incrBlk S₀ k' hcard).1
  have hfrng : Work.DSM5b.tupRng f = S₀ := (Work.DSM5b.HCF.incrBlk S₀ k' hcard).2
  have hmono : StrictMono f := fun i j hij => Work.DSM5b.HCF.isIncr_incrBlk S₀ k' hcard i j hij
  have hfinj : Function.Injective f := hmono.injective
  -- `g0` is injective because its range `S₀` has the same cardinality as its domain.
  have hsinj : Function.Injective g0 := by
    have h1 : (Finset.univ.image g0).card = (Finset.univ : Finset (Fin (k' + 1))).card := by
      rw [← Work.DSM5b.tupRng, hg0, Finset.card_univ, Fintype.card_fin]
      exact hcard.symm
    have h2 : Set.InjOn g0 ↑(Finset.univ : Finset (Fin (k' + 1))) := Finset.card_image_iff.mp h1
    intro x y hxy
    exact h2 (Finset.mem_univ x) (Finset.mem_univ y) hxy
  have heq : Work.DSM5b.tupRng g0 = Work.DSM5b.tupRng f := hg0.trans hfrng.symm
  -- For every position there is a position of `f` carrying the same entry.
  have hex : ∀ i : Fin (k' + 1), ∃ j : Fin (k' + 1), f j = g0 i := by
    intro i
    have hmem : g0 i ∈ Work.DSM5b.tupRng f :=
      heq ▸ (Finset.mem_image_of_mem g0 (Finset.mem_univ i))
    rcases Finset.mem_image.mp hmem with ⟨j, _, hj⟩
    exact ⟨j, hj⟩
  let g : Fin (k' + 1) → Fin (k' + 1) := fun i => Classical.choose (hex i)
  have hgspec : ∀ i, f (g i) = g0 i := fun i => Classical.choose_spec (hex i)
  -- `g` is onto, and hence a permutation of `Fin (k' + 1)`.
  have hgsurj : Function.Surjective g := by
    intro j
    have hmem : f j ∈ Work.DSM5b.tupRng g0 :=
      heq.symm ▸ (Finset.mem_image_of_mem f (Finset.mem_univ j))
    rcases Finset.mem_image.mp hmem with ⟨i, _, hi⟩
    exact ⟨i, hfinj (by rw [hgspec i]; exact hi)⟩
  have hginj : Function.Injective g := by
    intro i i' h
    exact hsinj (by rw [← hgspec i, ← hgspec i', h])
  refine ⟨Equiv.ofBijective g ⟨hginj, hgsurj⟩, ?_⟩
  funext i
  simp only [Function.comp_apply]
  exact (hgspec i).symm

end Work.DSM5b.HCF
