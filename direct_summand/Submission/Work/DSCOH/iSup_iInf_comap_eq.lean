import Mathlib

/-!
# Interchange of `iSup`/`iInf` under `comap` along a finite family

For a finite family of linear maps `g i : M →ₗ[R] N i` and a family of submodules
`D k i ⊆ N i` which is monotone in `k` (for each `i`), the `iSup` over `k` of the
`iInf` over `i` of the preimages commutes with the `iInf` over `i`:

`(⨆ k, ⨅ i, comap (g i) (D k i)) = ⨅ i, comap (g i) (⨆ k, D k i)`.

The `≤` direction is formal (preimage is monotone and a right adjoint, hence
preserves infima). The `≥` direction is where finiteness of the index type `ι`
and monotonicity of `D` in `k` are used: an element of the right hand side has
`g i x ∈ D (k i) i` for individual `k i`, and one may take the maximum of the
finitely many `k i` to find a single index `K` with `g i x ∈ D K i` for all `i`.
-/

namespace Work.DSCOH

theorem iSup_iInf_comap_eq {R : Type*} [Semiring R] {ι : Type*} [Fintype ι]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {N : ι → Type*} [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (g : ∀ i, M →ₗ[R] N i) (D : ℕ → ∀ i, Submodule R (N i))
    (hD : ∀ i, Monotone (fun k => D k i)) :
    (⨆ k, ⨅ i, Submodule.comap (g i) (D k i)) = ⨅ i, Submodule.comap (g i) (⨆ k, D k i) := by
  classical
  apply le_antisymm
  · -- `≤`: preimage is monotone and preserves arbitrary infima.
    refine iSup_le fun k => le_iInf fun i => ?_
    exact le_trans (iInf_le (fun i => Submodule.comap (g i) (D k i)) i)
      (Submodule.comap_mono (le_iSup (fun k' => D k' i) k))
  · -- `≥`: use finiteness of `ι` and monotonicity in `k` to take a common index.
    intro x hx
    rw [Submodule.mem_iInf] at hx
    have hx' : ∀ i, g i x ∈ ⨆ k, D k i := fun i => (Submodule.mem_comap).mp (hx i)
    choose K hK using fun i =>
      (Submodule.mem_iSup_of_directed (fun k => D k i) (hD i).directed_le).mp (hx' i)
    refine le_iSup (fun k => ⨅ i, Submodule.comap (g i) (D k i)) (Finset.univ.sup K) ?_
    rw [Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_comap]
    exact hD i (Finset.le_sup (Finset.mem_univ i)) (hK i)

end Work.DSCOH
