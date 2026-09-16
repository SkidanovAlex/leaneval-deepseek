import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

namespace Commons.Combinatorics.TupleCount

open List

/-- `Σ r : Fin N, Fin r → α` is equivalent to the sigma type over the subtype `{n // n < N}`. -/
private noncomputable def sigmaFinSubtype (N : ℕ) (α : Type*) :
    (Σ r : Fin N, Fin r → α) ≃ (Σ x : {n // n < N}, Fin x.1 → α) where
  toFun x := ⟨⟨x.1.1, x.1.2⟩, x.2⟩
  invFun x := ⟨⟨x.1.1, x.1.2⟩, x.2⟩
  left_inv := by rintro ⟨⟨r,hr⟩, f⟩; rfl
  right_inv := by rintro ⟨⟨n,hn⟩, f⟩; rfl

/-- Tuples of length `< N` over `α` (indexed by `Fin N`) are equivalent to lists of length `< N`. -/
private noncomputable def equivSigmaFinList (N : ℕ) (α : Type*) :
    (Σ r : Fin N, Fin r → α) ≃ {l : List α // l.length < N} :=
  (sigmaFinSubtype N α).trans <|
  ((Equiv.subtypeSigmaEquiv (fun n : ℕ => Fin n → α) (fun n => n < N)).symm).trans <|
  (Equiv.subtypeEquiv List.equivSigmaTuple.symm (fun s => by
    rw [List.equivSigmaTuple_symm_apply, List.length_ofFn]))

private lemma equivSigmaFinList_apply_val (N : ℕ) (α : Type*) (x : Σ r : Fin N, Fin r → α) :
    (equivSigmaFinList N α x).1 = List.ofFn x.2 := by
  simp only [equivSigmaFinList, Equiv.trans_apply, Equiv.subtypeEquiv_apply,
    Equiv.subtypeSigmaEquiv, List.equivSigmaTuple_symm_apply]
  rfl

/-- Lists of `Fin (2q)` (of length `< 2q`) that are "admissible tuples" are in bijection with
compositions of `n` with no block divisible by `q`. -/
private noncomputable def lacqEquiv (q n : ℕ) (hn : n < 2 * q) :
    {l : List (Fin (2 * q)) // l.length < 2 * q ∧
        ((∀ x ∈ l, 1 ≤ ((x : Fin (2 * q)) : ℕ) ∧ ¬ q ∣ ((x : Fin (2 * q)) : ℕ)) ∧
        (l.map Fin.val).sum = n)}
      ≃ {c : Composition n // ∀ b ∈ c.blocks, ¬ q ∣ b} where
  toFun l :=
    ⟨{ blocks := l.1.map Fin.val
       blocks_pos := by
         intro i hi
         rw [List.mem_map] at hi
         obtain ⟨x, hx, rfl⟩ := hi
         have hx1 := (l.2.2.1 x hx).1
         omega
       blocks_sum := l.2.2.2 },
     fun b hb => by
       rw [List.mem_map] at hb
       obtain ⟨x, hx, rfl⟩ := hb
       exact (l.2.2.1 x hx).2⟩
  invFun c :=
    ⟨List.pmap (fun b (hb : b < 2 * q) => (⟨b, hb⟩ : Fin (2 * q))) c.1.blocks
       (fun b hb => by
          have h1 : b ≤ c.1.blocks.sum := List.le_sum_of_mem hb
          rw [c.1.blocks_sum] at h1
          omega),
     by
       refine ⟨?_, ?_, ?_⟩
       · rw [List.length_pmap]
         have h1 : c.1.blocks.length ≤ n := c.1.length_le
         omega
       · intro x hx
         rw [List.mem_pmap] at hx
         obtain ⟨a, ha, heq⟩ := hx
         rw [← heq]
         exact ⟨c.1.one_le_blocks ha, c.2 a ha⟩
       · rw [List.map_pmap]
         rw [List.pmap_eq_map]
         rw [List.map_id']
         exact c.1.blocks_sum⟩
  left_inv := by
    rintro ⟨l, hl⟩
    apply Subtype.ext
    apply List.ext_getElem
    · rw [List.length_pmap, List.length_map]
    · intro i h1 h2
      simp only [List.getElem_pmap, List.getElem_map]
  right_inv := by
    rintro ⟨c, hc⟩
    apply Subtype.ext
    apply Composition.ext
    apply List.ext_getElem
    · rw [List.length_map, List.length_pmap]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_pmap]

theorem card_eq_composition (q n : ℕ) (hn : n < 2 * q) :
    Nat.card {x : Σ r : Fin (2 * q), Fin r → Fin (2 * q) //
        (∀ j, 1 ≤ ((x.2 j : Fin (2 * q)) : ℕ)) ∧
        (∀ j, ¬ (q ∣ ((x.2 j : Fin (2 * q)) : ℕ))) ∧
        (∑ j, ((x.2 j : Fin (2 * q)) : ℕ)) = n}
      = Nat.card {c : Composition n // ∀ b ∈ c.blocks, ¬ q ∣ b} := by
  refine Nat.card_congr ?_
  refine (Equiv.subtypeEquiv (equivSigmaFinList (2 * q) (Fin (2 * q)))
      (q := fun b => (∀ x ∈ b.1, 1 ≤ ((x : Fin (2 * q)) : ℕ) ∧ ¬ q ∣ ((x : Fin (2 * q)) : ℕ)) ∧
        (b.1.map Fin.val).sum = n) ?_).trans ?_
  · intro x
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_⟩
      · rw [equivSigmaFinList_apply_val]
        rw [List.forall_mem_ofFn_iff]
        exact fun j => ⟨h1 j, h2 j⟩
      · rw [equivSigmaFinList_apply_val]
        rw [List.map_ofFn, List.sum_ofFn]; exact h3
    · rintro ⟨h1, h2⟩
      rw [equivSigmaFinList_apply_val] at h1 h2
      refine ⟨?_, ?_, ?_⟩
      · intro j; exact (List.forall_mem_ofFn_iff.1 h1 j).1
      · intro j; exact (List.forall_mem_ofFn_iff.1 h1 j).2
      · rw [List.map_ofFn, List.sum_ofFn] at h2; exact h2
  · exact (Equiv.subtypeSubtypeEquivSubtypeInter (fun l : List (Fin (2 * q)) => l.length < 2 * q)
      (fun l => (∀ x ∈ l, 1 ≤ ((x : Fin (2 * q)) : ℕ) ∧ ¬ q ∣ ((x : Fin (2 * q)) : ℕ)) ∧
        (l.map Fin.val).sum = n)).trans (lacqEquiv q n hn)

end Commons.Combinatorics.TupleCount