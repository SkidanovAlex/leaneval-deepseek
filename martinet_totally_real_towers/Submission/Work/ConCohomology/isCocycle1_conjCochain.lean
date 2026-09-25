/-
Copyright: the martinet_totally_real_towers team.

# The conjugation action on `Z¹(N, M)`

Fix a group extension `1 → N → G → Q → 1` encoded as `GroupExt G Q N` and a `G`-module `M`
whose `N`-action is the restriction of the `G`-action along `i` (`hcompN`).  Conjugation by
`g : G` acts on `1`-cochains on `N` by `φ ↦ (n ↦ g • φ (conj g⁻¹ n))`; this is the action
underlying the restriction map `H¹(N, M) → H¹(G, M)` in the five term sequence.

This module proves that this operation preserves the `1`-cocycle condition, i.e. that it
descends to `Z¹(N, M)`.  Two elementary inputs are isolated as separate lemmas:

* conjugation is multiplicative in its second argument (`GroupExt.conj_map_mul`);
* `g • ((conj g)⁻¹ n • m) = n • (g • m)`, which is where `hcompN` is used
  (`GroupExt.smul_conj_smul`).
-/

import Mathlib
import Submission.Work.ConCohomology.Extension

set_option linter.unusedVariables false

namespace Work.ConCohomology

/-- Conjugation by `g` is multiplicative in its second argument.  This is immediate from
`i (conj g n) = g * i n * g⁻¹` and injectivity of `i`. -/
lemma GroupExt.conj_map_mul {G Q N : Type*} [Group G] [Group Q] [Group N]
    (E : GroupExt G Q N) (g : G) (n m : N) :
    E.conj g (n * m) = E.conj g n * E.conj g m := by
  apply E.injective_i
  simp only [map_mul, E.i_conj]
  group

/-- Compatibility of the two actions: since the `N`-action on `M` is the restriction of the
`G`-action along `i`, conjugating the acting element by `g` and then acting is the same as
acting with `g` after conjugation by `g⁻¹`. -/
lemma GroupExt.smul_conj_smul {G Q N : Type*} [Group G] [Group Q] [Group N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
    (E : GroupExt G Q N) (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m)
    (g : G) (n : N) (m : M) :
    g • ((E.conj g⁻¹ n) • m) = n • (g • m) := by
  rw [hcompN (E.conj g⁻¹ n) m, ← mul_smul, E.i_conj, hcompN n (g • m), ← mul_smul]
  congr 1
  group

/-- The conjugation action of `G` on `1`-cochains on `N` preserves the cocycle condition:
if `φ : N → M` is a `1`-cocycle for the `N`-action, then so is `n ↦ g • φ (conj g⁻¹ n)`. -/
lemma isCocycle1_conjCochain {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] (E : GroupExt G Q N)
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m)
    (hcont : ∀ g : G, Continuous (E.conj g)) (g : G) {φ : N → M}
    (hφ : IsCocycle1 φ) : IsCocycle1 (fun n : N => g • φ (E.conj g⁻¹ n)) := by
  intro n m
  simp only []
  rw [GroupExt.conj_map_mul, hφ, smul_add,
    GroupExt.smul_conj_smul E hcompN g n (φ (E.conj g⁻¹ m))]

end Work.ConCohomology
