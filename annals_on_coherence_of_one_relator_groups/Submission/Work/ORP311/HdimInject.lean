/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (the dimension-theoretic injectivity step of the Følner/Lück argument)

# The dimension-theoretic injectivity step (`dim V ≤ dim S V` for injective equivariant maps)

This is step (13)/(14) of the Følner--Lück approximation argument for the locally indicable
case ([Jaikin, *L²-Betti numbers and their analogues in positive characteristic*, Groups
St Andrews 2017, LNS 455, Theorem 12.1], the input of [JZLA20, Corollary 12.2] /
Proposition 3.11):

> if a bounded `H`-equivariant map `S` is *injective* on an `H`-invariant closed subspace `V`,
> then `dim V ≤ dim S(V)`.

In the concrete von Neumann model of `Work.ORVonNeumann.Rep` the statement reads: for an
operator `T` on `HSum n = ⊕_{i<n} ℓ²(G)` which is `Equivariant` (commutes with the block
diagonal right regular action `diagOp n g`) and a `diagOp`-invariant closed subspace `K`,
injectivity of `T` on `K` gives

  `hdim K ≤ hdim (closure (T(K)))`,

indeed equality of the two von Neumann dimensions.

The proof is rank--nullity for equivariant operators: the composite `S = T ∘ P_K` is again
equivariant, its kernel is `Kᗮ` (by injectivity of `T` on `K`) and the closure of its range is
the closure of `T(K)`; `Work.ORVonNeumann.Rep.vnBAK_index_equivariant` gives
`hdim S.ker = hdim S†.ker` and `S†.kerᗮ = closure (S.range)`, while
`Work.ORVonNeumann.Rep.vnHdimCompl` gives `hdim K + hdim Kᗮ = n`.

## Main result

* `Work.ORP311.hdim_le_hdim_range_of_injective` — the dimension estimate;
* `Work.ORP311.hdim_eq_hdim_range_of_injective` — the underlying equality.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnBlockUpperAdjointKernel

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

/-- **The dimension of a `diagOp`-invariant closed subspace is preserved by an injective
equivariant operator.**  Equality form: `hdim K = hdim (closure (T(K)))`.

Here `T` is a bounded operator on `HSum n`, `Equivariant (G := G) T` says that it commutes with
the block diagonal right regular action, `K` is a closed subspace with an orthogonal projection
which is invariant under that action, and `T` is injective on `K`. -/
theorem hdim_eq_hdim_range_of_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (T : Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n)
    (hT : Rep.Equivariant (G := G) T)
    (K : Submodule ℂ (Rep.HSum (G := G) n)) [K.HasOrthogonalProjection]
    (hK : ∀ g : G, ∀ x ∈ K, Rep.diagOp (G := G) n g x ∈ K)
    (hinj : ∀ x ∈ K, T x = 0 → x = 0) :
    Rep.hdim (G := G) K
      = Rep.hdim (G := G) (T.comp K.starProjection).range.topologicalClosure := by
  -- `S = T ∘ P_K` is equivariant.
  have hS : Rep.Equivariant (G := G) (T.comp K.starProjection) :=
    Rep.Equivariant.comp (Rep.equivariant_starProjection (G := G) hK) hT
  -- Its kernel is `Kᗮ`.
  have hker : (T.comp K.starProjection).ker = Kᗮ := by
    ext x
    show (T.comp K.starProjection) x = 0 ↔ x ∈ Kᗮ
    rw [Submodule.mem_orthogonal']
    constructor
    · intro hx u hu
      have h0 : K.starProjection x = 0 :=
        hinj _ (Submodule.starProjection_apply_mem K x) hx
      have h1 : x - K.starProjection x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
      have h2 : inner ℂ (x - K.starProjection x) u = 0 :=
        (Submodule.mem_orthogonal' K (x - K.starProjection x)).mp h1 u hu
      simpa [inner_sub_left, h0] using h2
    · intro hx
      have hmem : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
      have horth : inner ℂ x (K.starProjection x) = 0 := hx _ hmem
      have hsub : inner ℂ (x - K.starProjection x) (K.starProjection x) = 0 :=
        Submodule.starProjection_inner_eq_zero x (K.starProjection x) hmem
      have hsq : inner ℂ (K.starProjection x) (K.starProjection x) = 0 := by
        rw [inner_sub_left] at hsub
        rw [horth, zero_sub] at hsub
        exact neg_eq_zero.mp hsub
      have h0 : K.starProjection x = 0 := inner_self_eq_zero.mp hsq
      simp [h0]
  -- Rank--nullity (index identity) for `S`, and the complement identities.
  have hidx := Rep.vnBAK_index_equivariant (G := G) (T.comp K.starProjection) hS
  have hSker : Rep.hdim (G := G) (T.comp K.starProjection).ker
      = Rep.hdim (G := G) (ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker := by
    linarith
  have hSkerK : Rep.hdim (G := G) (T.comp K.starProjection).ker = Rep.hdim (G := G) Kᗮ :=
    Rep.hdim_congr (G := G) hker
  have hcomplK : Rep.hdim (G := G) K + Rep.hdim (G := G) Kᗮ = (n : ℝ) :=
    Rep.vnHdimCompl (G := G) (K := K)
  have hcomplS : Rep.hdim (G := G) (ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker
      + Rep.hdim (G := G) ((ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker)ᗮ
      = (n : ℝ) :=
    Rep.vnHdimCompl (G := G)
      (K := (ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker)
  have horth : ((ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker)ᗮ
      = (T.comp K.starProjection).range.topologicalClosure := by
    rw [ContinuousLinearMap.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint]
  have hrange : Rep.hdim (G := G) (T.comp K.starProjection).range.topologicalClosure
      = Rep.hdim (G := G) ((ContinuousLinearMap.adjoint (T.comp K.starProjection)).ker)ᗮ :=
    Rep.hdim_congr (G := G) horth.symm
  linarith

/-- **The dimension-theoretic injectivity inequality**: for an injective equivariant operator
on `HSum n` and a `diagOp`-invariant closed subspace `K`, `hdim K ≤ hdim (closure (T(K)))`. -/
theorem hdim_le_hdim_range_of_injective {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ}
    (T : Rep.HSum (G := G) n →L[ℂ] Rep.HSum (G := G) n)
    (hT : Rep.Equivariant (G := G) T)
    (K : Submodule ℂ (Rep.HSum (G := G) n)) [K.HasOrthogonalProjection]
    (hK : ∀ g : G, ∀ x ∈ K, Rep.diagOp (G := G) n g x ∈ K)
    (hinj : ∀ x ∈ K, T x = 0 → x = 0) :
    Rep.hdim (G := G) K
      ≤ Rep.hdim (G := G) (T.comp K.starProjection).range.topologicalClosure :=
  le_of_eq (hdim_eq_hdim_range_of_injective (G := G) T hT K hK hinj)

end Work.ORP311
