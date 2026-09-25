/-
Copyright: the martinet_totally_real_towers team.

# The inner action on `H¹(N, M)` is trivial

Fix a group extension `1 → N → G → Q → 1`, encoded as `GroupExt G Q N`, and a `G`-module `M`
whose `N`-action is the restriction of the `G`-action along `i` (`hcompN`).  Conjugation by
`g : G` acts on `1`-cochains on `N` by `φ ↦ (n ↦ g • φ (conj g⁻¹ n))`.

This module proves that conjugation by an element of the image of `i` acts through a coboundary:
for `φ : N → M` a `1`-cocycle for the `N`-action one has

  `conjCochain E hcont (i n) φ - φ = d⁰ (φ n)`,

i.e. the inner automorphisms of `N` induced by `N` act trivially on `H¹(N, M)`.  Consequently the
`Q`-action on `H¹(N, M)` relevant to the transgression in the five term sequence factors through
`H¹(N,M)/`(inner action), and in particular the conjugation action descends to `H¹(N,M)` without
any `Q`-equivariance input.

The proof is the standard computation: writing `g = i n`,

  `g • φ (conj g⁻¹ x) - φ x = n • φ (n⁻¹ x n) - φ x = n • φ n⁻¹ + (φ x + x • φ n) - φ x`,

and `n • φ n⁻¹ = -φ n` because `φ` is a crossed homomorphism with `φ 1 = 0`.  So the difference is
`x • φ n - φ n = d⁰(φ n) (x)`.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension

set_option linter.unusedVariables false

namespace Work.ConCohomology

open Function Classical

section Helpers

/-- Conjugation by `i n` inverts to conjugation by `n⁻¹` inside `N`, i.e.
`i (conj (i n)⁻¹ x) = i n⁻¹ * i x * i n`.  This is immediate from `i_conj` and injectivity of `i`. -/
lemma GroupExt.conj_i_inv {G Q N : Type*} [Group G] [Group Q] [Group N] (E : GroupExt G Q N)
    (n x : N) : E.conj (E.i n)⁻¹ x = n⁻¹ * x * n := by
  apply E.injective_i
  rw [E.i_conj]
  simp only [map_mul, map_inv]
  group

/-- A `1`-cocycle vanishes at the identity: `f 1 = f 1 + 1 • f 1`. -/
lemma isCocycle1_apply_one {N : Type*} [Group N] {M : Type*} [AddCommGroup M]
    [DistribMulAction N M] {f : N → M} (hf : IsCocycle1 f) : f 1 = 0 := by
  have h3 := hf 1 1
  simp only [mul_one, one_smul] at h3
  have := congrArg (fun y : M => y - f 1) h3
  simpa [eq_comm] using this

/-- For a `1`-cocycle `f` and `n : N` one has `n • f n⁻¹ = -f n`; this is the cocycle identity
for the pair `(n, n⁻¹)` together with `f 1 = 0`. -/
lemma isCocycle1_smul_inv {N : Type*} [Group N] {M : Type*} [AddCommGroup M]
    [DistribMulAction N M] {f : N → M} (hf : IsCocycle1 f) (n : N) : n • f n⁻¹ = -f n := by
  have h2 := hf n n⁻¹
  rw [mul_inv_cancel, isCocycle1_apply_one hf] at h2
  exact eq_neg_of_add_eq_zero_right h2.symm

end Helpers

lemma conjCochain_inner {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] (E : GroupExt G Q N)
    (hcompN : ∀ (n : N) (m : M), n • m = E.i n • m)
    (hcont : ∀ g : G, Continuous (E.conj g)) (n : N) {φ : Cochain1 N M}
    (hφ : IsCocycle1 (φ : N → M)) :
    ∃ m : M, ((conjCochain E hcont (E.i n) φ : N → M) - (φ : N → M)) =
      d0Fun (G := N) m := by
  refine ⟨φ n, ?_⟩
  funext x
  show (E.i n) • φ (E.conj (E.i n)⁻¹ x) - φ x = x • φ n - φ n
  rw [E.conj_i_inv, ← hcompN n (φ (n⁻¹ * x * n))]
  have h1 : φ (n⁻¹ * x * n) = φ n⁻¹ + n⁻¹ • (φ x + x • φ n) := by
    rw [mul_assoc, hφ n⁻¹ (x * n), hφ x n]
  rw [h1, smul_add, ← mul_smul, mul_inv_cancel, one_smul, isCocycle1_smul_inv hφ n]
  abel

end Work.ConCohomology
