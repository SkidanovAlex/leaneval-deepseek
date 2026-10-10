import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.SSGRoute.PTW.avgOp_regRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The spectral step: from `avgOp ξ` to a finite-dimensional invariant subspace on which `y` acts
nontrivially.

Auxiliary file for `Work.SSGRoute.PTW.mem_all_open_index_p_iff_mem_closure_pthPowers`.

## The refined argument (this is the critical path)

Fix `ξ ≠ 0` with `(regRep y - 1) ξ ≠ 0`, and put `A := avgOp ξ` (compact, self-adjoint, `≠ 0`).
Write `E_λ = eigenspace A λ`.

1. `avgOp_regRep` (PROVED, delegated): `A (regRep h η) = regRep h (A η)`; hence every `E_λ` is
   `regRep`-invariant, and `regRep h` restricts to a linear isometry equivalence of `E_λ`.
2. `compact_selfAdjoint_range_le_iSup_eigenspace` (statement reviewed, to be proved):
   `A.range ≤ (⨆ (λ : {λ // λ ≠ 0}), E_λ).topologicalClosure`.
3. `⟨Aη, η⟩ = ∫ g, ‖⟪regRep g ξ, η⟫‖² ∂μ` and `⟨Aξ, ξ⟩ > 0`, so `A ≠ 0` and
   `η ∈ ker A → ∀ g, ⟪regRep g ξ, η⟫ = 0`, i.e. `ker A ≤ (orbit of ξ)^⊥`.
4. Consequence: `∃ λ ≠ 0` with `E_λ ≠ ⊥` and `regRep y ≠ 1` on `E_λ`.
   Indeed, if `regRep y = 1` on every `E_λ` (λ ≠ 0), then `regRep y = 1` on the closure of their
   span (continuity), so by (2) `(regRep y - 1) (A η) = A ((regRep y - 1) η) = 0` for all `η`,
   i.e. `(regRep y - 1) ξ ∈ ker A ≤ (orbit of ξ)^⊥`.  Then `(regRep y - 1) ξ ⊥ ξ` and
   `⊥ regRep y ξ`, so `⟪regRep y ξ, ξ⟫ = ‖ξ‖² = ‖regRep y ξ‖ ‖ξ‖`, and equality in
   Cauchy–Schwarz forces `regRep y ξ = ξ`, contradicting the choice of `ξ`.
5. `E_λ` is finite-dimensional (Mathlib `ContinuousLinearMap.finite_dimensional_eigenspace`) and
   `regRep y ≠ 1` on it; then `finiteDim_rep_exists_weight` gives a character `χ : Q →* ℂˣ` with
   `χ y ≠ 1` and an eigenvector, and `χ` is automatically continuous in finite dimension.

## Status

`regularRep`: DONE (sorry-free).  `avgOp_regRep`: PROVED by a colleague.
Requested/reviewed but not yet spawned: `avgOp_isSymmetric`, `avgOp_ne_zero`, `avgOp_isCompact`,
`compact_selfAdjoint_range_le_iSup_eigenspace`, `finiteDim_rep_exists_weight`.
## Sibling line of work in this directory (READ IT)

`NOTES.md` records a parallel effort (other sessions) on the *sibling* target
`mem_pthPower_of_all_open_index_p_subgroups` (the `C_K` version).  It does NOT solve this crux but
it has banked useful proven lemmas, all importable:

* `Work.SSGRoute.PTW.connectedComponentOfOne_le_of_isOpen_subgroup` (PROVED): every open subgroup of
  a topological group contains the identity component.  (This gives the reduction "the hypothesis
  only sees `x̄ ∈ G ⧸ G₀`" used by the sibling; note it does NOT replace the crux here, since
  `G₀ ⊆ (p-th powers)` is exactly divisibility of `G₀`, i.e. the same difficulty in disguise.)
* `Work.SSGRoute.PTW.map_connectedComponentOfOne_eq_of_surjective` (PROVED).
* `torus_divisible.lean`, `openIndexPSubgroup.lean`,
  `exists_open_index_p_notMem_of_totallyDisconnected_exponent` (PROVED; the latter is the L2 lemma
  already used by the target file).

## Note on the target file

`mem_all_open_index_p_iff_mem_closure_pthPowers.lean` currently imports a *missing* module
`Submission.Work.SSGRoute.PTW.compact_abelian_exponent_p_totallyDisconnected`.  The plan is to
replace that dependency by `exists_open_index_p_notMem_of_compact_abelian_exponent_p` (to be proved
from this file): the hard direction of the target needs exactly "in a compact abelian group of
exponent `p`, a nonidentity element lies outside some open index-`p` subgroup".
-/

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The eigenspaces of the averaging operator are invariant under the regular representation. -/
theorem avgOp_regRep_mem_eigenspace (ξ : Lp ℂ 2 μ) (h : Q) (lam : ℂ) {η : Lp ℂ 2 μ}
    (hη : η ∈ Module.End.eigenspace
      ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam) :
    regRep (μ := μ) h η ∈ Module.End.eigenspace
      ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam := by
  rw [Module.End.mem_eigenspace_iff] at hη ⊢
  change (avgOp (μ := μ) ξ) η = lam • η at hη
  change (avgOp (μ := μ) ξ) (regRep (μ := μ) h η) = lam • regRep (μ := μ) h η
  rw [avgOp_regRep, hη, map_smul]

/-- A compact self-adjoint nonzero operator has a nonzero eigenvalue. -/
theorem exists_eigenvalue_ne_zero (ξ : Lp ℂ 2 μ)
    (hc : IsCompactOperator ⇑(avgOp (μ := μ) ξ))
    (hs : ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
      Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).IsSymmetric)
    (hn : avgOp (μ := μ) ξ ≠ 0) :
    ∃ lam : ℂ, lam ≠ 0 ∧ Module.End.eigenspace
      ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) lam ≠ ⊥ := by
  by_contra h
  push_neg at h
  have h0 : ∀ t : ℂ, Module.End.HasEigenvalue
      ((avgOp (μ := μ) ξ : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) t → t = 0 := by
    intro t ht
    by_contra htne
    exact ht (h t htne)
  exact hn ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hc hs).mp h0)

end Work.SSGRoute.PTW
