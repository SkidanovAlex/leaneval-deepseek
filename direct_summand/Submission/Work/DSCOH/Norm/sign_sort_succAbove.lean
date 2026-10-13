/-
# The sign of the stable sorting permutation of a tuple with one entry deleted

`Tuple.sort z` is the *stable* sorting permutation of the tuple `z : Fin (n+1) → ι`
(ties are broken by the position).  If we delete the entry at position `j`, the tuple
`fun i : Fin n => z (j.succAbove i)` is again sorted by its own stable sorting
permutation `Tuple.sort (z ∘ j.succAbove)`, a permutation of `Fin n`.

The main theorem of this file computes the sign of the latter in terms of the sign of
the former:

  `sign (sort (z ∘ j.succAbove)) = sign (sort z) * (-1) ^ (j + σ⁻¹ j)`,  where `σ = sort z`.

The mathematical content is:

* `sort_comp_succAbove`: `σ ∘ succAbove (σ⁻¹ j) = succAbove j ∘ τ` where `σ = sort z` and
  `τ = sort (z ∘ succAbove j)`.  Both sides are the increasing enumeration (for the
  lexicographic order on the pairs `(z x, x)`) of the complement of `j`; this is proved with
  the uniqueness of such an enumeration (`Finset.orderEmbOfFin_unique`).

* `sign_eq_of_succAbove_fix`: a permutation of `Fin (n+1)` fixing `j` and inducing `τ` on the
  complement of `j` has the same sign as `τ` (`Equiv.Perm.sign_bij`).

* `exists_succAbove_shift`: there is a permutation `c` of `Fin (n+1)` with `c j = σ⁻¹ j`,
  `c ∘ succAbove j = succAbove (σ⁻¹ j)` and `sign c = (-1) ^ (j + σ⁻¹ j)`: it is the cyclic
  shift of the interval between the two positions (`Fin.cycleIcc`) oriented suitably.

Multiplying `σ` by `c` on the right makes it fix `j`; the sign formula follows.
-/

import Mathlib

namespace Work.DSCOH.Norm

open Equiv Prod.Lex

/-! ## The stable sorting permutation is compatible with deleting an entry -/

/-- The defining property of `Tuple.sort`: the pairs `(f (sort f i), sort f i)` are strictly
increasing for the lexicographic order. -/
lemma strictMono_pair_of_eq_sort {α : Type*} [LinearOrder α] {m : ℕ} {f : Fin m → α}
    {σ : Equiv.Perm (Fin m)} (h : σ = Tuple.sort f) :
    StrictMono (fun i => toLex ((f (σ i), σ i) : α × Fin m)) := by
  subst h
  intro i i' hii
  obtain ⟨hmono, hstab⟩ := (Tuple.eq_sort_iff (f := f) (σ := Tuple.sort f)).mp rfl
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_trichotomy (f (Tuple.sort f i)) (f (Tuple.sort f i')) with h | h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, hstab i i' hii h⟩
  · exact absurd (hmono hii.le) (not_le.mpr h)

/-- Deleting the `σ⁻¹ j`-th entry of the (stably) sorted tuple `z ∘ σ`, where `σ = Tuple.sort z`,
and the deletion `succAbove j`, agree up to the stable sorting of `Fin n`:  if `σ = Tuple.sort z`
and `τ = Tuple.sort (z ∘ succAbove j)` then `σ ∘ succAbove (σ⁻¹ j) = succAbove j ∘ τ`.

Both sides are the strictly increasing enumeration, for the lexicographic order on the pairs
`(z x, x)`, of the complement of `j`. -/
lemma sort_comp_succAbove {ι : Type*} [LinearOrder ι] {n : ℕ} (z : Fin (n+1) → ι)
    (j : Fin (n+1)) :
    (Tuple.sort z) ∘ (Fin.succAbove ((Tuple.sort z).symm j)) =
      Fin.succAbove j ∘ (Tuple.sort (z ∘ Fin.succAbove j)) := by
  set σ := Tuple.sort z with hσ
  set k : Fin (n+1) := σ.symm j with hk
  set τ := Tuple.sort (z ∘ Fin.succAbove j) with hτ
  have hσk : σ k = j := by rw [hk]; exact Equiv.apply_symm_apply σ j
  -- the finite set `s` of pairs `(z x, x)` with `x ≠ j`
  set s : Finset (ι ×ₗ Fin (n+1)) :=
    (Tuple.graph z).erase (toLex ((z j, j) : ι × Fin (n+1))) with hs
  have hmem : toLex ((z j, j) : ι × Fin (n+1)) ∈ Tuple.graph z := by
    rw [Tuple.graph]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  have hcard : s.card = n := by
    rw [hs, Finset.card_erase_of_mem hmem, Tuple.graph.card]
    omega
  -- the first candidate: `i ↦ (z (σ (k.succAbove i)), σ (k.succAbove i))`
  have hf1 : StrictMono (fun i : Fin n =>
      toLex ((z (σ (k.succAbove i)), σ (k.succAbove i)) : ι × Fin (n+1))) :=
    (strictMono_pair_of_eq_sort hσ).comp (Fin.strictMono_succAbove k)
  -- the second candidate: `i ↦ (z (succAbove j (τ i)), succAbove j (τ i))`
  have hpair : StrictMono (fun i : Fin n =>
      toLex (((z ∘ Fin.succAbove j) (τ i), τ i) : ι × Fin n)) :=
    strictMono_pair_of_eq_sort hτ
  have hF : StrictMono (fun q : ι ×ₗ Fin n =>
      toLex (((ofLex q).1, Fin.succAbove j (ofLex q).2) : ι × Fin (n+1))) := by
    intro a b hab
    rw [Prod.Lex.lt_iff] at hab ⊢
    rcases hab with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, (Fin.strictMono_succAbove j) h2⟩
  have hf2 : StrictMono (fun i : Fin n =>
      toLex ((z (Fin.succAbove j (τ i)), Fin.succAbove j (τ i)) : ι × Fin (n+1))) :=
    hF.comp hpair
  have hf1mem : ∀ i : Fin n, (fun i : Fin n =>
      toLex ((z (σ (k.succAbove i)), σ (k.succAbove i)) : ι × Fin (n+1))) i ∈ s := by
    intro i
    rw [hs, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hcon
      have h2 : σ (k.succAbove i) = j := by
        have := congrArg (fun t : ι × Fin (n+1) => t.2) (Equiv.injective toLex hcon)
        exact this
      have : k.succAbove i = k := σ.injective (by rw [h2, hσk])
      exact Fin.succAbove_ne k i this
    · rw [Tuple.graph]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hf2mem : ∀ i : Fin n, (fun i : Fin n =>
      toLex ((z (Fin.succAbove j (τ i)), Fin.succAbove j (τ i)) : ι × Fin (n+1))) i ∈ s := by
    intro i
    rw [hs, Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hcon
      have h2 : Fin.succAbove j (τ i) = j := by
        have := congrArg (fun t : ι × Fin (n+1) => t.2) (Equiv.injective toLex hcon)
        exact this
      exact Fin.succAbove_ne j (τ i) h2
    · rw [Tuple.graph]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have e1 := Finset.orderEmbOfFin_unique hcard hf1mem hf1
  have e2 := Finset.orderEmbOfFin_unique hcard hf2mem hf2
  have hfun : (fun i : Fin n =>
        toLex ((z (σ (k.succAbove i)), σ (k.succAbove i)) : ι × Fin (n+1)))
      = (fun i : Fin n =>
        toLex ((z (Fin.succAbove j (τ i)), Fin.succAbove j (τ i)) : ι × Fin (n+1))) := by
    rw [e1, e2]
  funext i
  have h2 := congrFun hfun i
  exact congrArg (fun t : ι ×ₗ Fin (n+1) => (ofLex t).2) h2

/-! ## The sign of a permutation fixing a point -/

/-- If `ρ : Perm (Fin (n+1))` fixes `j` and induces `τ` on the complement of `j`
(identified with `Fin n` via `j.succAbove`), then `ρ` and `τ` have the same sign. -/
lemma sign_eq_of_succAbove_fix {n : ℕ} (ρ : Equiv.Perm (Fin (n+1))) (j : Fin (n+1))
    (τ : Equiv.Perm (Fin n)) (hfix : ρ j = j)
    (h : ρ ∘ Fin.succAbove j = Fin.succAbove j ∘ τ) :
    Equiv.Perm.sign ρ = Equiv.Perm.sign τ := by
  refine (Equiv.Perm.sign_bij (f := τ) (g := ρ) (i := fun x _ => Fin.succAbove j x)
    ?_ ?_ ?_).symm
  · intro x hx hx'
    exact (congrFun h x).symm
  · intro x₁ x₂ hx₁ hx₂ heq
    exact Fin.succAbove_right_injective heq
  · intro y hy
    have hyj : y ≠ j := fun hc => hy (by rw [hc, hfix])
    obtain ⟨x, hx⟩ := Fin.exists_succAbove_eq hyj
    refine ⟨x, fun htx => hy ?_, hx⟩
    calc ρ y = ρ (j.succAbove x) := by rw [hx]
      _ = j.succAbove (τ x) := congrFun h x
      _ = j.succAbove x := by rw [htx]
      _ = y := hx

/-! ## The cyclic shift between two positions -/

/-- `(-1 : ℤˣ) ^ a` only depends on the parity of `a`. -/
lemma negOne_pow_eq_of_mod_two {a b : ℕ} (h : a % 2 = b % 2) :
    (-1 : ℤˣ) ^ a = (-1 : ℤˣ) ^ b := by
  have h2 : (-1 : ℤˣ) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod a h2, pow_eq_pow_mod b h2, h]

/-- For any two positions `j`, `k` of `Fin (n+1)` there is a permutation `c` which sends `j` to
`k`, intertwines the two "deletion" embeddings (`c ∘ succAbove j = succAbove k`) and has sign
`(-1) ^ (j + k)`: the cyclic shift of the interval between `j` and `k`, oriented so that it
sends `j` to `k`. -/
lemma exists_succAbove_shift {n : ℕ} (j k : Fin (n+1)) :
    ∃ c : Equiv.Perm (Fin (n+1)), c j = k ∧ c ∘ Fin.succAbove j = Fin.succAbove k ∧
      Equiv.Perm.sign c = (-1 : ℤˣ) ^ ((j:ℕ) + (k:ℕ)) := by
  rcases le_total k j with hkj | hjk
  · refine ⟨Fin.cycleIcc k j, ?_, ?_, ?_⟩
    · exact Fin.cycleIcc_of_last hkj
    · exact Fin.cycleIcc_comp_succAbove k j hkj
    · rw [Fin.sign_cycleIcc_of_le hkj]
      exact negOne_pow_eq_of_mod_two (by omega)
  · refine ⟨(Fin.cycleIcc j k).symm, ?_, ?_, ?_⟩
    · rw [Equiv.symm_apply_eq]
      exact (Fin.cycleIcc_of_last hjk).symm
    · funext x
      have hcomp := congrFun (Fin.cycleIcc_comp_succAbove j k hjk) x
      simp only [Function.comp_apply] at hcomp ⊢
      rw [← hcomp, Equiv.symm_apply_apply]
    · rw [Equiv.Perm.sign_symm, Fin.sign_cycleIcc_of_le hjk]
      exact negOne_pow_eq_of_mod_two (by omega)

/-! ## The sign relation -/

/-- If `σ ∘ succAbove (σ⁻¹ j) = succAbove j ∘ τ` for `σ : Perm (Fin (n+1))` and
`τ : Perm (Fin n)`, then `sign τ = sign σ * (-1) ^ (j + σ⁻¹ j)`. -/
lemma sign_eq_of_comp_succAbove {n : ℕ} (σ : Equiv.Perm (Fin (n+1))) (j : Fin (n+1))
    (τ : Equiv.Perm (Fin n))
    (h : σ ∘ Fin.succAbove (σ.symm j) = Fin.succAbove j ∘ τ) :
    Equiv.Perm.sign τ =
      Equiv.Perm.sign σ * (-1 : ℤˣ) ^ ((j:ℕ) + ((σ.symm j : Fin (n+1)) : ℕ)) := by
  obtain ⟨c, hcj, hccomp, hcsign⟩ := exists_succAbove_shift j (σ.symm j)
  have hfix : (σ * c) j = j := by
    rw [Equiv.Perm.mul_apply, hcj, Equiv.apply_symm_apply]
  have hcomp : (σ * c) ∘ Fin.succAbove j = Fin.succAbove j ∘ τ := by
    rw [Equiv.Perm.coe_mul, Function.comp_assoc, hccomp, h]
  have hmain := sign_eq_of_succAbove_fix (σ * c) j τ hfix hcomp
  rw [Equiv.Perm.sign_mul, hcsign] at hmain
  exact hmain.symm

/-- The sign of the stable sorting permutation of the tuple with the `j`-th entry deleted, in
terms of the sign of the stable sorting permutation of the tuple. -/
theorem sign_sort_succAbove {ι : Type*} [LinearOrder ι] {n : ℕ} (z : Fin (n+1) → ι) (j : Fin (n+1)) :
    ((Equiv.Perm.sign (Tuple.sort (fun i : Fin n => z (j.succAbove i))) : ℤˣ) : ℤ) =
      ((Equiv.Perm.sign (Tuple.sort z) : ℤˣ) : ℤ) *
        (-1) ^ ((j : ℕ) + (((Tuple.sort z).symm j : Fin (n+1)) : ℕ)) := by
  have h1 := sort_comp_succAbove z j
  have h2 := sign_eq_of_comp_succAbove (Tuple.sort z) j
    (Tuple.sort (fun i : Fin n => z (j.succAbove i))) h1
  have h3 := congrArg (fun u : ℤˣ => (u : ℤ)) h2
  simpa [Units.val_mul, Units.val_pow_eq_pow_val] using h3

end Work.DSCOH.Norm
