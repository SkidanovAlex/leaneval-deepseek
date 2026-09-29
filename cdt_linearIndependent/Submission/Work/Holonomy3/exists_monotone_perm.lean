import Mathlib
import Submission.Work.Holonomy3.comp_defs

namespace Work.Holonomy3

/-- **Sorting a finite family of natural numbers by a permutation.**
For every `n : Fin d → ℕ` there is a permutation `π` of `Fin d` such that `n ∘ π` is monotone:
`π` lists the indices in nondecreasing order of the values of `n`.

Proof: order the indices by the key `(n i, i)` in the lexicographic order on `ℕ × Fin d`. This key
is injective, so its image `s` is a finset of cardinality `d`, and `s.orderIsoOfFin` enumerates `s`
in increasing order. Passing to the second component of the inverse enumeration produces the
permutation `π`; monotonicity is the fact that `toLex` is monotone in the first component. -/
theorem exists_monotone_perm {d : ℕ} (n : Fin d → ℕ) :
    ∃ π : Equiv.Perm (Fin d), Monotone (n ∘ π) := by
  classical
  -- the index `i` is recorded together with its value `n i`, so that the key is injective
  let κ : Fin d → (ℕ ×ₗ Fin d) := fun i => toLex (n i, i)
  have hκ : Function.Injective κ := by
    intro i j hij
    exact congrArg Prod.snd (toLex_inj.mp hij)
  -- the keys of all indices, as a finset of the same cardinality
  let s : Finset (ℕ ×ₗ Fin d) := Finset.univ.map ⟨κ, hκ⟩
  have hcard : s.card = d := by simp [s]
  -- increasing enumeration of the keys
  let e : Fin d ≃o ↥s := s.orderIsoOfFin hcard
  -- every key in the enumeration is the key of some index
  have hmem : ∀ k : Fin d, ∃ i : Fin d, κ i = ((e k : ↥s) : (ℕ ×ₗ Fin d)) := by
    intro k
    have h : ((e k : ↥s) : (ℕ ×ₗ Fin d)) ∈ s := (e k).2
    rw [Finset.mem_map] at h
    obtain ⟨i, -, hi⟩ := h
    exact ⟨i, hi⟩
  -- the corresponding index: this is the permutation
  let πfun : Fin d → Fin d := fun k => Classical.choose (hmem k)
  have hπfun : ∀ k, κ (πfun k) = ((e k : ↥s) : (ℕ ×ₗ Fin d)) :=
    fun k => Classical.choose_spec (hmem k)
  -- it is injective, because it is a section of an injective map
  have hπinj : Function.Injective πfun := by
    intro a b hab
    have hh : κ (πfun a) = κ (πfun b) := by rw [hab]
    have h : ((e a : ↥s) : (ℕ ×ₗ Fin d)) = ((e b : ↥s) : (ℕ ×ₗ Fin d)) :=
      (hπfun a).symm.trans (hh.trans (hπfun b))
    exact e.injective (Subtype.ext h)
  have hbij : Function.Bijective πfun := ⟨hπinj, (Finite.injective_iff_surjective.mp hπinj)⟩
  -- monotonicity of `n ∘ πfun`, from the increasing enumeration of the keys
  have hmono : Monotone (n ∘ πfun) := by
    intro a b hab
    have h1 : e a ≤ e b := (e.le_iff_le).mpr hab
    have h2 : κ (πfun a) ≤ κ (πfun b) := by
      rw [hπfun a, hπfun b]
      exact h1
    change toLex (n (πfun a), πfun a) ≤ toLex (n (πfun b), πfun b) at h2
    rw [Prod.Lex.toLex_le_toLex] at h2
    rcases h2 with h | ⟨h, -⟩
    · exact le_of_lt h
    · exact le_of_eq h
  refine ⟨Equiv.ofBijective πfun hbij, ?_⟩
  have hcomp : (Equiv.ofBijective πfun hbij : Fin d → Fin d) = πfun :=
    funext (Equiv.ofBijective_apply πfun hbij)
  rw [hcomp]
  exact hmono

end Work.Holonomy3
