/-
# Block decompositions of the fixed point set of an element of a `p`-group

This file sets up the vocabulary used by `Work.LocalPrelim.rsf_block_decomposition`.

Given a group `P` acting on a type `O`, an element `x : P` and a set `Ω ⊆ O`, a *block decomposition*
of `Ω` (relative to `x`) is a finite family of maps `e i : ZMod p → O` together with witnesses
`y i : P` such that

* `e i` is injective (so `(e i k)_k` enumerates a `p`-element subset, a "block"),
* `y i` cyclically permutes the block: `y i • e i k = e i (k + 1)`,
* `(y i) ^ p` fixes the block pointwise,
* the blocks are pairwise disjoint (the last field) and their union is exactly `Ω`.

This is the shape of the conclusion of the Feit--Thompson "regular Sylow" analysis of the fixed
points of an element of a `p`-group acting on a set: the fixed points (other than the unique
`P`-fixed point) split into `p`-cycles of elements of `P`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

universe u v

/-- `IsBlockDecomp p x Ω n e y` says that the maps `e i : ZMod p → O` (`i : Fin n`), together with
the witnesses `y i : P`, decompose the set `Ω ⊆ O` into pairwise disjoint `p`-element blocks which
are cyclically permuted by the `y i`, while `(y i) ^ p` fixes each block pointwise. -/
structure IsBlockDecomp (p : ℕ) {P : Type u} {O : Type v} [Group P] [MulAction P O] (x : P)
    (Ω : Set O) (n : ℕ) (e : Fin n → ZMod p → O) (y : Fin n → P) : Prop where
  /-- every `e i` is injective -/
  injective : ∀ i, Function.Injective (e i)
  /-- `y i` cyclically permutes the `i`-th block -/
  shift : ∀ i k, y i • e i k = e i (k + 1)
  /-- `(y i) ^ p` fixes the `i`-th block pointwise -/
  pow_fix : ∀ i k, (y i) ^ p • e i k = e i k
  /-- the blocks are contained in `Ω` -/
  mem : ∀ i k, e i k ∈ Ω
  /-- every element of `Ω` is covered by a block -/
  exists_of_mem : ∀ a, a ∈ Ω → ∃ i k, e i k = a
  /-- distinct blocks are disjoint -/
  eq_iff : ∀ i k j l, e i k = e j l → i = j ∧ k = l

namespace IsBlockDecomp

variable {p : ℕ} {P : Type u} {O : Type v} [Group P] [MulAction P O]

/-- Block decompositions are transported along equivariant injections. -/
theorem map {P₂ : Type*} {O₂ : Type*} [Group P₂] [MulAction P₂ O₂] (φ : P →* P₂)
    {f : O → O₂} (hf : Function.Injective f) (hcomp : ∀ (g : P) (a : O), f (g • a) = φ g • f a)
    {x : P} {Ω : Set O} {n : ℕ} {e : Fin n → ZMod p → O} {y : Fin n → P}
    (h : IsBlockDecomp p x Ω n e y) :
    IsBlockDecomp p (φ x) (f '' Ω) n (fun i k => f (e i k)) (fun i => φ (y i)) where
  injective i := hf.comp (h.injective i)
  shift i k := by rw [← hcomp, h.shift]
  pow_fix i k := by rw [← map_pow, ← hcomp, h.pow_fix]
  mem i k := ⟨e i k, h.mem i k, rfl⟩
  exists_of_mem a ha := by
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨i, k, hik⟩ := h.exists_of_mem b hb
    exact ⟨i, k, by rw [hik]⟩
  eq_iff i k j l h' := h.eq_iff i k j l (hf h')

end IsBlockDecomp

end Work.LocalPrelim
