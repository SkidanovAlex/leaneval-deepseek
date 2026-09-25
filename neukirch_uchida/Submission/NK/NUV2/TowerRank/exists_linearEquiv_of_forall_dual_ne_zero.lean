import Mathlib

/-!
# A submodule of `ℤ_ℓ^r` detected by every nonzero functional is isomorphic to `ℤ_ℓ^r`

Let `R = ℤ_ℓ` (the `ℓ`-adic integers, a discrete valuation ring, hence a PID) and
`M = R^r = Fin r → R`.  If `N ≤ M` is a submodule such that **every** nonzero `R`-linear
functional `f : M →ₗ[R] R` is nonzero on *some* element of `N` (equivalently, the restriction
map `Dual R M → Dual R N` is injective, equivalently the annihilator of `N` in the dual of `M`
is zero), then `N` is `R`-linearly isomorphic to `M`.

The proof uses the Smith normal form of the inclusion `N ↪ M` over the PID `R`
(`Submodule.smithNormalForm`): there are bases `bM` of `M` (indexed by `Fin r`), `bN` of `N`
(indexed by `Fin n`) and an embedding `f : Fin n ↪ Fin r` with `bN i = a i • bM (f i)`.
If `j : Fin r` were *not* in the range of `f`, then the coordinate functional `bM.coord j`
would vanish on `N` (`Module.Basis.SmithNormalForm.le_ker_coord_of_notMem_range`) while being
nonzero, contradicting the hypothesis.  Hence `f` is surjective, so `n = r`, and reindexing
`bN` along `Fin n ≃ Fin r` and applying `Basis.equivFun` gives the required linear equivalence.
-/

namespace NK.NUV2.TowerRank

open Module

theorem exists_linearEquiv_of_forall_dual_ne_zero {ℓ r : ℕ} [Fact ℓ.Prime]
    (N : Submodule (PadicInt ℓ) (Fin r → PadicInt ℓ))
    (h : ∀ f : Module.Dual (PadicInt ℓ) (Fin r → PadicInt ℓ), f ≠ 0 → ∃ x ∈ N, f x ≠ 0) :
    Nonempty (N ≃ₗ[PadicInt ℓ] (Fin r → PadicInt ℓ)) := by
  classical
  -- Smith normal form of the inclusion `N ↪ ℤ_ℓ^r`.
  obtain ⟨n, snf⟩ := Submodule.smithNormalForm (Pi.basisFun (PadicInt ℓ) (Fin r)) N
  -- Every index of the basis of `M` is hit by the embedding attached to the Smith normal form,
  -- since a missed index would give a nonzero functional killing `N`.
  have hsurj : Function.Surjective snf.f := by
    intro j
    by_contra hj
    have hjmem : j ∉ Set.range snf.f := fun hmem => hj hmem
    have hker : N ≤ LinearMap.ker (snf.bM.coord j) := snf.le_ker_coord_of_notMem_range hjmem
    have hne : snf.bM.coord j ≠ 0 := by
      intro hzero
      have h1 : snf.bM.coord j (snf.bM j) = 1 := by simp
      rw [hzero, LinearMap.zero_apply] at h1
      exact one_ne_zero h1.symm
    obtain ⟨x, hxN, hxne⟩ := h (snf.bM.coord j) hne
    exact hxne (hker hxN)
  -- Hence the basis of `N` has the same size as the basis of `M`.
  have hcard : n = r := by
    have h1 : n ≤ r := by simpa using Fintype.card_le_of_injective snf.f snf.f.injective
    have h2 : r ≤ n := by simpa using Fintype.card_le_of_surjective snf.f hsurj
    omega
  obtain ⟨e⟩ : Nonempty (Fin n ≃ Fin r) := ⟨Fintype.equivOfCardEq (by simp [hcard])⟩
  exact ⟨(snf.bN.reindex e).equivFun⟩

end NK.NUV2.TowerRank
