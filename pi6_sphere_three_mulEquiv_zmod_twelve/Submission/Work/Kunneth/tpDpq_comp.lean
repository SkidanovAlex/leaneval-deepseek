import Mathlib
import Submission.Work.Kunneth.TensorDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Koszul differential of the tensor product vanishes on a summand

`Work.Kunneth.tpDpq C D n pq` is the `(p,q)`-summand of the Koszul differential
`x ⊗ y ↦ d x ⊗ y + (-1)^p x ⊗ d y` of the tensor product of two chain complexes of
`ℤ`-modules (`Submission/Work/Kunneth/TensorDefs.lean`), and `Work.Kunneth.tpD C D n`
is its sum over all bidegrees `p + q = n + 1`.

This file proves `Work.Kunneth.tpDpq_comp`, the statement that the composite
`tpD C D n ∘ tpDpq C D (n + 1) pq` is zero on the summand `C_p ⊗ D_q`.  This is
the "single summand" form of the identity `∂ ∘ ∂ = 0` for the Koszul differential.

The proof is an explicit element computation: applying the expansion of `tpD`
and `tpDpq` twice produces the two terms `d(dx) ⊗ y` (killed by `d_d_apply`) and
`(-1)^{p-1} • dx ⊗ dy + (-1)^p • dx ⊗ dy` (killed by `neg_one_pow_pred_add`).

## A note on instances

The scalar multiplication of `LinearMap`s occurring in the *definition* of
`tpDpq` is the one derived from `ZSMul` (via `instHSMul`/`ZSMul.toSMul`), whereas the
generic lemmas `LinearMap.map_smul`/`smul_apply` are stated for the scalar structure
coming from `Module`.  These are *propositionally* but not *definitionally* equal, so
`rw`/`simp` fail to apply the generic lemmas to those particular occurrences.  The
lemma `smul_lmap_apply` below is stated with `[AddCommGroup]` hypotheses (rather than
`[AddCommMonoid]`), which makes typeclass search pick the same `ZSMul`-derived
scalar structure, so that it can be used as a rewrite rule.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The scalar multiplication of `LinearMap`s is the pointwise one:
`(c • f) x = c • f x`.  Stated with `AddCommGroup` hypotheses so that the scalar
structures are the `ZSMul`-derived ones, which is what the definition of `tpDpq` uses. -/
theorem smul_lmap_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N]
    (c : ℤ) (f : M →ₗ[ℤ] N) (x : M) : (c • f) x = c • f x := rfl

/-- The sign identity `(-1)^(p-1) + (-1)^p = 0` for `p ≥ 1`. -/
theorem neg_one_pow_pred_add (p : ℕ) (hp : 1 ≤ p) :
    (-1 : ℤ) ^ (p - 1) + (-1 : ℤ) ^ p = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [show k + 1 - 1 = k by omega, pow_succ]
  ring

/-- **The Koszul differential vanishes on a summand after a second application.** -/
theorem tpDpq_comp (C D : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (pq : Work.Kunneth.tpIdx (n + 2)) :
    LinearMap.comp (Work.Kunneth.tpD C D n) (Work.Kunneth.tpDpq C D (n + 1) pq) = 0 := by
  obtain ⟨⟨p, q⟩, hpq⟩ := pq
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  erw [tpDpq_tmul]
  simp only [Subtype.coe_mk]
  rw [LinearMap.map_add]
  rw [apply_dite (tpD C D n) (1 ≤ p), apply_dite (tpD C D n) (1 ≤ q)]
  simp only [map_zero]
  simp only [map_zsmul]
  rw [tpD]
  simp only [DirectSum.toModule_lof]
  split_ifs with hp hq
  · -- main case: `1 ≤ p` and `1 ≤ q`
    simp only [tpDpq]
    simp only [LinearMap.add_apply]
    split_ifs <;> try simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    all_goals first | (exfalso; omega) | skip
    all_goals repeat (first | erw [TensorProduct.map_tmul] | rw [smul_lmap_apply] | rw [LinearMap.comp_apply] | rw [LinearMap.id_apply] | rw [LinearMap.zero_apply] | rw [d_d_apply] | rw [TensorProduct.zero_tmul] | rw [TensorProduct.tmul_zero] | rw [map_zero])
    all_goals repeat (first | rw [zsmul_add] | rw [zsmul_zero] | rw [zero_add] | rw [add_zero])
    all_goals try rw [← add_zsmul]
    all_goals try rw [neg_one_pow_pred_add p hp]
    all_goals try rw [zero_zsmul]
    all_goals try rfl
  · -- `1 ≤ p` but `¬ 1 ≤ q`, so `q = 0`
    obtain rfl : q = 0 := by omega
    simp only [tpDpq]
    simp only [LinearMap.add_apply]
    split_ifs <;> try simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    all_goals first | (exfalso; omega) | skip
    all_goals repeat (first | erw [TensorProduct.map_tmul] | rw [smul_lmap_apply] | rw [LinearMap.comp_apply] | rw [LinearMap.id_apply] | rw [LinearMap.zero_apply] | rw [d_d_apply] | rw [TensorProduct.zero_tmul] | rw [TensorProduct.tmul_zero] | rw [map_zero])
    all_goals repeat (first | rw [zsmul_add] | rw [zsmul_zero] | rw [zero_add] | rw [add_zero])
    all_goals try rw [← add_zsmul]
    all_goals try rw [neg_one_pow_pred_add p hp]
    all_goals try rw [zero_zsmul]
    all_goals try rfl
  · -- `¬ 1 ≤ p`, so `p = 0`, and `1 ≤ q`
    obtain rfl : p = 0 := by omega
    simp only [tpDpq]
    simp only [LinearMap.add_apply]
    split_ifs <;> try simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    all_goals first | (exfalso; omega) | skip
    all_goals repeat (first | erw [TensorProduct.map_tmul] | rw [smul_lmap_apply] | rw [LinearMap.comp_apply] | rw [LinearMap.id_apply] | rw [LinearMap.zero_apply] | rw [d_d_apply] | rw [TensorProduct.zero_tmul] | rw [TensorProduct.tmul_zero] | rw [map_zero])
    all_goals repeat (first | rw [zsmul_add] | rw [zsmul_zero] | rw [zero_add] | rw [add_zero])
    all_goals try rw [← add_zsmul]
    all_goals try rw [neg_one_pow_pred_add p hp]
    all_goals try rw [zero_zsmul]
    all_goals try rfl
  · -- `¬ 1 ≤ p` and `¬ 1 ≤ q`
    rw [zero_add]

end

end Work.Kunneth
