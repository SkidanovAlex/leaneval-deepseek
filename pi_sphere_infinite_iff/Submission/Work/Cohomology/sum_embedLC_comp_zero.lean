import Mathlib
import Submission.Work.Cohomology.Subdivision

/-!
# The simplicial identity `∑ᵢⱼ (-1)^{i+j} δᵢ δⱼ = 0` for the face embeddings

`embedLC N k i : LinChain N k →ₗ[ℤ] LinChain (N+1) k` is the `i`-th *face embedding* of affine
chains: it post-composes every vertex of a vertex family with the order embedding
`Fin.succAbove i : Fin (N+1) → Fin (N+2)`.

This file proves that the "second boundary" of the two-step face embeddings vanishes
(`sum_embedLC_comp_zero`):

`∑_{i : Fin (m+3)} ∑_{j : Fin (m+2)} (-1)^{i+j} (embedLC (m+1) m i ∘ₗ embedLC m m j) = 0`.

The mechanism is the classical simplicial identity `δᵢ δⱼ = δ_{j'} δ_{i'}` with reversed sign:
the composite `succAbove i ∘ succAbove j` only depends on the *two-element set*
`{i, succAbove i j}` omitted from `Fin (m+3)`, and the two pairs `(i,j)` realising a given set
differ by an odd shift of `i + j`, hence carry opposite signs.  Concretely the involution

`g (i, j) = (succAbove i j, predAbove j i)`

is fixed-point free (`Fin.succAbove_ne`), has `g ∘ g = id` (`Fin.succAbove_succAbove_predAbove`,
`Fin.predAbove_predAbove_succAbove`), flips the parity of `i + j`
(`Fin.neg_one_pow_succAbove_add_predAbove`) and preserves the composite
(`Fin.succAbove_succAbove_succAbove_predAbove`); so the sum pairs off and vanishes.
-/

namespace Work.Cohomology

noncomputable section

/-- The `ℤ`-linear map on affine chains induced by a map `σ : Fin (m+1) → Fin (m+3)` of vertex
sets: every vertex of a vertex family is pushed forward by `stdSimplex.map σ`.  This is the common
shape of all two-step composites of face embeddings. -/
private def sigMap (m : ℕ) (σ : Fin (m + 1) → Fin (m + 3)) :
    LinChain m m →ₗ[ℤ] LinChain (m + 2) m :=
  Finsupp.lmapDomain ℤ ℤ
    (fun v : Fin (m + 1) → stdSimplex ℝ (Fin (m + 1)) => fun t => stdSimplex.map σ (v t))

/-- A two-step composite of face embeddings is the `sigMap` of the composite order embedding. -/
private lemma embedLC_comp_eq (m : ℕ) (i : Fin (m + 3)) (j : Fin (m + 2)) :
    embedLC (m + 1) m i ∘ₗ embedLC m m j
      = sigMap m ((Fin.succAbove i).comp (Fin.succAbove j)) := by
  simp only [sigMap, embedLC]
  rw [← Finsupp.lmapDomain_comp]
  congr 1
  funext v t
  exact (stdSimplex.map_comp_apply (Fin.succAbove j) (Fin.succAbove i) (v t))

theorem sum_embedLC_comp_zero (m : ℕ) :
    (∑ p : Fin (m + 3) × Fin (m + 2),
        ((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) •
          (embedLC (m + 1) m p.1 ∘ₗ embedLC m m p.2)) = 0 := by
  simp only [embedLC_comp_eq]
  let f : Fin (m + 3) × Fin (m + 2) → (LinChain m m →ₗ[ℤ] LinChain (m + 2) m) :=
    fun p => ((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) •
      sigMap m ((Fin.succAbove p.1).comp (Fin.succAbove p.2))
  let g : Fin (m + 3) × Fin (m + 2) → Fin (m + 3) × Fin (m + 2) :=
    fun p => (Fin.succAbove p.1 p.2, Fin.predAbove p.2 p.1)
  have hsign : ∀ (i : Fin (m + 3)) (j : Fin (m + 2)),
      ((-1 : ℤ) ^ ((Fin.succAbove i j : ℕ) + (Fin.predAbove j i : ℕ)))
        = -((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) := by
    intro i j
    simpa using Fin.neg_one_pow_succAbove_add_predAbove (R := ℤ) i j
  have hsig : ∀ (i : Fin (m + 3)) (j : Fin (m + 2)),
      (Fin.succAbove (Fin.succAbove i j)).comp (Fin.succAbove (Fin.predAbove j i))
        = (Fin.succAbove i).comp (Fin.succAbove j) := by
    intro i j
    funext k
    exact Fin.succAbove_succAbove_succAbove_predAbove i j k
  have key : (∑ p : Fin (m + 3) × Fin (m + 2), f p) = 0 := by
    refine Finset.sum_ninvolution (s := Finset.univ) g ?_ ?_ ?_ ?_
    · intro a
      have h : f (g a) = -f a := by
        obtain ⟨i, j⟩ := a
        simp only [f, g]
        rw [hsign i j, hsig i j, neg_smul]
      rw [h, add_neg_cancel]
    · intro a _
      obtain ⟨i, j⟩ := a
      intro h
      have h1 : (Fin.succAbove i j) = i := by
        simpa [g] using congrArg Prod.fst h
      exact Fin.succAbove_ne i j h1
    · intro a
      exact Finset.mem_univ _
    · intro a
      obtain ⟨i, j⟩ := a
      simp only [g]
      rw [Fin.succAbove_succAbove_predAbove i j, Fin.predAbove_predAbove_succAbove i j]
  simpa [f] using key

end

end Work.Cohomology
