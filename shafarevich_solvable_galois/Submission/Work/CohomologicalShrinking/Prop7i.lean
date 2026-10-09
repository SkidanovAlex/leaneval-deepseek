/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proposition 7 (i) of Schmidt–Wingberg: the semidirect-product variant

Schmidt–Wingberg's **Proposition 7 (i)** is the variant of the shrinking lemma that is used in
step 4 of the proof of Theorem 15:

> for given elements `x₁, …, x_t ∈ H^{-2}(F(m)/F(m)^{(ν)} ⋊ G, E(m,τ) ⊗ T)` there exists `m₀ ≥ n`
> such that for all `m ≥ m₀` there is a surjective `G`-operator homomorphism `F(m) ⇢ F(n)` whose
> induced homomorphism kills all the `x_i`.

Its proof in the paper runs through the homological Hochschild–Serre exact sequence
(`H⁻² = H₁`)

`H₁(F(m)/ν, E⊗T) --α--> H₁(F(m)/ν ⋊ G, E⊗T) --β--> H₁(G, E⊗T) --→ 0`,

in which:

* `F(m)/ν` acts trivially on `E(m,τ) ⊗ T`, so by the universal coefficient formula the first
  term is `F(m)/F(m)² ⊗ E(m,τ) ⊗ T` (the model of Proposition 7 (ii) used in `Prop7.lean`);
* `α` is (the composite of) the surjections of Proposition 5 plus `F(m)/F(m)²`;

and the shrinking is a two-step diagram chase:

1. use Proposition 7 (ii) with target `ℓ` (or rather the `k = -2` case of Proposition 6, in the
   `I_G`-model `H₁(G, X) ≅ Ĥ⁻¹(G, X ⊗ I_G)`) with `ℓ₀` a fixed admissible level to find `m ≥ ℓ₀`
   and `Φ₁ : F(m) ⇢ F(ℓ₀)` killing `β(x_i)`;
2. exactness at the middle term shows `zMap Φ₁ (x_i) = α(u_i)` for some `u_i`, and Proposition
   7 (ii) for the target `n` provides `Φ₂ : F(ℓ₀) ⇢ F(n)` killing the `u_i`;
3. the composite `Φ₂ ∘ Φ₁` then kills the `x_i`, because `α` is natural in the rank.

Only the two structural inputs of this argument are *not* formalized in this workspace: the
homological Hochschild–Serre sequence for `F(m)/ν ⋊ G` (in particular the exactness
`range α = ker β` and the surjectivity of `β`), and the universal coefficient formula
`H₁(F(m)/ν, E⊗T) ≅ F(m)/F(m)² ⊗ E(m,τ) ⊗ T` (there is no `H₁` of a group in this workspace; see
`Work.Tate`'s `NOTES.md` §6).  They are therefore isolated here as the fields of the structure
`SemidirectShrinkingData`: a type family `Z m` modelling `H₁(F(m)/ν ⋊ G, E(m,τ) ⊗ T)` together
with `α`, `β`, their exactness, their naturality in the rank and the functoriality of the maps
`zMap Φ` induced by operator maps.  Given that data, the paper's chase is carried out here and
Prop 7 (i) follows — so the *mathematical* content of the paper's proof is proved, and the
isolated hypothesis is exactly the Hochschild–Serre bookkeeping.

## Main results

* `Work.CohomologicalShrinking.SemidirectShrinkingData` : the Hochschild–Serre data.
* `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect` : Proposition 7 (i).
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Levels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u v w

variable {p : ℕ}

/-- **The Hochschild–Serre data of Schmidt–Wingberg's Proposition 7 (i).**

`Z m` is a model of `H₁(F(m)/F(m)^{(ν)} ⋊ G, E(m,τ) ⊗ T) = Ĥ^{-2}(F(m)/ν ⋊ G, E(m,τ) ⊗ T)`,
`α m` is the map `H₁(F(m)/ν, E⊗T) = F(m)/F(m)² ⊗ E(m,τ) ⊗ T → Z m` from the homological
Hochschild–Serre sequence, and `β m` is the map `Z m → H₁(G, E⊗T) = Ĥ^{-2}(G, E⊗T)`, the latter
written in the `I_G`-model `Ĥ^{-2}(G, X) ≅ Ĥ⁻¹(G, X ⊗ I_G)`.  The fields record the exactness,
the surjectivity of `β`, the functoriality of the maps `zMap Φ : Z m → Z n` induced by a
surjective `G`-operator homomorphism `Φ : F(m) → F(n)`, and the naturality of `α` and `β` with
respect to those maps. -/
structure SemidirectShrinkingData (p : ℕ) [NeZero p] (G : Type*) [Group G] [Fintype G] (i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (Z : ℕ → Type*) [∀ m : ℕ, AddCommGroup (Z m)] [∀ m : ℕ, Module (ZMod p) (Z m)] where
  /-- `H₁(F(m)/ν, E(m,τ) ⊗ T) → H₁(F(m)/ν ⋊ G, E(m,τ) ⊗ T)`. -/
  α : ∀ m : ℕ,
    (squareQuotient p G m ⊗[ZMod p] (E p G m i j ⊗[ZMod p] T)) →+ Z m
  /-- `H₁(F(m)/ν ⋊ G, E(m,τ) ⊗ T) → H₁(G, E(m,τ) ⊗ T)`, in the `I_G`-model of `Ĥ^{-2}`. -/
  β : ∀ m : ℕ, Z m →+ Work.Tate.Hm1 G (E p G m i j ⊗[ZMod p] (T ⊗[ZMod p] augIdeal p G))
  /-- The map induced by an operator map. -/
  zMap : ∀ ⦃m n : ℕ⦄, OperatorMap G m n → (Z m →+ Z n)
  /-- Exactness at `H₁(F(m)/ν ⋊ G, E(m,τ) ⊗ T)`. -/
  exact_αβ : ∀ m : ℕ, (α m).range = (β m).ker
  /-- `H₁(G, E(m,τ) ⊗ T) → 0` is exact, i.e. `β m` is surjective. -/
  β_surjective : ∀ m : ℕ, (β m).range = ⊤
  /-- Functoriality of `zMap` in the rank. -/
  zMap_comp : ∀ ⦃m n l : ℕ⦄ (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l),
    zMap (Ψ.comp Φ) = (zMap Ψ).comp (zMap Φ)
  /-- Naturality of `α` in the rank. -/
  α_natural : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
    (zMap Φ).comp (α m) = (α n).comp (Φ.h1Map p G T).toAddMonoidHom
  /-- Naturality of `β` in the rank. -/
  β_natural : ∀ ⦃m n : ℕ⦄ (Φ : OperatorMap G m n),
    (Φ.hm1Map p G (T ⊗[ZMod p] augIdeal p G)).comp (β m) = (β n).comp (zMap Φ)

/-- **Proposition 7 (i) of Schmidt–Wingberg**, at every level `m ≥ m₀`.

Let `G` be a finite group, `p` a prime, `τ = (i,j)` with `j ≥ 1`, `T` a finitely generated
`𝔽_p[G]`-module, and let `SD` be the Hochschild–Serre data for `H₁(F(m)/ν ⋊ G, E(m,τ) ⊗ T)` (see
`SemidirectShrinkingData`).  Then there is `m₀ ≥ n` such that for all `m ≥ m₀` and all
`x₁, …, x_t ∈ H^{-2}(F(m)/ν ⋊ G, E(m,τ) ⊗ T)` there is a surjective `G`-equivariant
`Φ : F(m) → F(n)` whose induced homomorphism kills all the `x_i`.

The only unproved inputs are `Prop5Data` (Proposition 5) and the fields of `SD` (the
Hochschild–Serre exact sequence and the universal coefficient formula). -/
theorem exists_shrinking_H1_semidirect (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    {i j : ℕ} (hj : 1 ≤ j) (D : Prop5Data p G i j)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] [Module.Finite (ZMod p) T]
    (Z : ℕ → Type*) [∀ m : ℕ, AddCommGroup (Z m)] [∀ m : ℕ, Module (ZMod p) (Z m)]
    (SD : SemidirectShrinkingData p G i j T Z)
    (t : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀, ∀ x : Fin t → Z m,
      ∃ Φ : OperatorMap G m n, ∀ k : Fin t, SD.zMap Φ (x k) = 0 := by
  -- the level at which the classes of `H₁(G, ·)` (i.e. `Ĥ^{-2}`) are killed
  obtain ⟨ℓ₀, hnℓ₀, hℓ₀⟩ := exists_shrinking_H1 (p := p) G hj D T t hn
  have h1ℓ₀ : 1 ≤ ℓ₀ := le_trans hn hnℓ₀
  -- the levels at which the classes of `H₁(F(m)/ν, ·)` are killed
  obtain ⟨m₀, _hm₀n, hm₀⟩ := exists_shrinking_Hm2IG (p := p) G hj D T t (n := ℓ₀) h1ℓ₀
  refine ⟨max m₀ n, le_max_right m₀ n, fun m hm x => ?_⟩
  obtain ⟨Φ₁, hΦ₁⟩ := hm₀ m (le_trans (le_max_left m₀ n) hm) (fun k => SD.β m (x k))
  -- exactness: `zMap Φ₁ (x k)` is an `α`-image
  have hmem : ∀ k : Fin t, SD.zMap Φ₁ (x k) ∈ (SD.α ℓ₀).range := fun k => by
    rw [SD.exact_αβ ℓ₀, AddMonoidHom.mem_ker]
    have hnat := congrArg (fun f => f (x k)) (SD.β_natural Φ₁)
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at hnat
    rw [← hnat]
    exact hΦ₁ k
  choose u hu using hmem
  -- the second shrinking step
  obtain ⟨Φ₂, hΦ₂⟩ := hℓ₀ ℓ₀ le_rfl u
  refine ⟨Φ₂.comp Φ₁, fun k => ?_⟩
  have hαnat := congrArg (fun f => f (u k)) (SD.α_natural Φ₂)
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply] at hαnat
  calc SD.zMap (Φ₂.comp Φ₁) (x k)
      = SD.zMap Φ₂ (SD.zMap Φ₁ (x k)) := by
        rw [SD.zMap_comp, AddMonoidHom.comp_apply]
    _ = SD.zMap Φ₂ (SD.α ℓ₀ (u k)) := by rw [hu k]
    _ = SD.α n (Φ₂.h1Map p G T (u k)) := hαnat
    _ = 0 := by rw [hΦ₂ k, map_zero]

end Work.CohomologicalShrinking
