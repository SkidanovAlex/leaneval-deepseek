import Mathlib
import Submission.Work.Cohomology.Singular
import Submission.Work.Cohomology.relComplex_vanishing_of_homology_free
import Submission.Work.Cohomology.relChains_empty_homology_iso
import Submission.Work.Cohomology.relComplex_empty_homology_iso
import Submission.Work.Cohomology.euclidean_open_homology_vanishing
import Submission.Work.Cohomology.euclidean_top_homology_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

/-!
# Vanishing of the cohomology of an open subset of `ℝ^N` above the dimension

For an open subset `U ⊆ ℝ^N` (`N ≥ 1`) the singular cohomology with `ℤ`-coefficients vanishes in
every degree `k ≥ N`:

  `Hᵏ(U; ℤ) = 0`  for `k ≥ N`.

This is the cohomological dimension bound for open subsets of Euclidean space: an open subset of
`ℝ^N` is an `N`-manifold without compact components, hence has cohomological dimension `≤ N - 1`.
It is the input behind the local vanishing `H^j(M, M∖K) = 0` (`j > N`, `K` compact) of an
`N`-manifold, used throughout the Poincaré duality chapter.

## The argument

The statement is reduced to two *homological* inputs, which are far more accessible than the
cohomological one:

* `euclidean_open_homology_vanishing` — `H_m(U) = 0` for every `m ≥ N` (an open subset of `ℝ^N`
  is a connected-by-component non-compact `N`-manifold, Hatcher, *Algebraic Topology*,
  Proposition 3.29);
* `euclidean_top_homology_free` — `H_{N-1}(U)` is a free abelian group (Alexander duality
  `H_{N-1}(U) ≅ H̃⁰(S^N ∖ U)`, the free group on the components of the complement in
  `S^N = ℝ^N ∪ {∞}`).

Then the universal coefficient theorem in the single degree where *both* of its terms vanish
(`relComplex_vanishing_of_homology_free`) gives the vanishing of `H^k(U; ℤ)`: for `k ≥ N + 1` both
`H_k(U)` and `H_{k-1}(U)` vanish, while for `k = N` one uses `H_N(U) = 0` together with the
freeness of `H_{N-1}(U)` (`Hom(H_N, ℤ) = 0` and `Ext(H_{N-1}, ℤ) = 0`).

The relative chains and cochains of the empty set are the absolute ones
(`relChains_empty_homology_iso`, `relComplex_empty_homology_iso`), so the relative form of the
theorem applies directly to `U`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- A subsingleton transfers across an isomorphism of `ℤ`-modules. -/
theorem subsingleton_of_iso_aux {P Q : ModuleCat ℤ} (e : P ≅ Q) (h : Subsingleton P) :
    Subsingleton Q :=
  (Equiv.subsingleton_congr e.toLinearEquiv.toEquiv).mp h

/-- **The cohomology of an open subset of `ℝ^N` vanishes above the dimension**, reduced to the
homology vanishing in degrees `≥ N` and the freeness of `H_{N-1}`. -/
theorem euclidean_open_cohomology_vanishing_of_inputs {N : ℕ} (hN : 1 ≤ N)
    (U : Set (EuclideanSpace ℝ (Fin N)))
    (hHom : ∀ m, N ≤ m → IsZero ((singularChains ℤ (TopCat.of ↥U)).homology m))
    (hFree : Module.Free ℤ ↥((singularChains ℤ (TopCat.of ↥U)).homology (N - 1))) :
    ∀ k, N ≤ k → Subsingleton
      ((singularCochainComplex ℤ (TopCat.of ↥U)).homology k) := by
  intro k hk
  have hk1 : 1 ≤ k := le_trans hN hk
  have hisoR : ∀ m, IsIso (HomologicalComplex.homologyMap
      (Limits.cokernel.π (inclChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U)))) m) :=
    fun m => relChains_empty_homology_iso (TopCat.of ↥U) m
  -- `h1`: vanishing of `H_k(relChains)`
  have h1 : IsZero ((relChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U))).homology k) := by
    haveI := hisoR k
    exact IsZero.of_iso (hHom k hk) (asIso (HomologicalComplex.homologyMap
      (Limits.cokernel.π (inclChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U)))) k)).symm
  -- `h0`: freeness of `H_{k-1}(relChains)`
  have h0 : Module.Free ℤ
      ↥((relChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U))).homology (k - 1)) := by
    have hmono : N - 1 ≤ k - 1 := Nat.sub_le_sub_right hk 1
    have hsrc : Module.Free ℤ ↥((singularChains ℤ (TopCat.of ↥U)).homology (k - 1)) := by
      rcases lt_or_eq_of_le hmono with h | h
      · have hz : IsZero ((singularChains ℤ (TopCat.of ↥U)).homology (k - 1)) :=
          hHom (k - 1) (by omega)
        haveI : Subsingleton ↥((singularChains ℤ (TopCat.of ↥U)).homology (k - 1)) :=
          ModuleCat.isZero_iff_subsingleton.mp hz
        exact Module.Free.of_subsingleton ℤ _
      · have hk' : k = N := by omega
        rw [hk']
        exact hFree
    haveI := hsrc
    haveI := hisoR (k - 1)
    exact Module.Free.of_equiv (asIso (HomologicalComplex.homologyMap
      (Limits.cokernel.π (inclChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U)))) (k - 1))).toLinearEquiv
  -- the universal-coefficient input in one degree
  have hS : Subsingleton ((relComplex ℤ (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U))).homology k) := by
    have h1' : IsZero ((relChains (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U))).homology ((k - 1) + 1)) := by
      rwa [Nat.sub_add_cancel hk1]
    simpa [Nat.sub_add_cancel hk1] using relComplex_vanishing_of_homology_free
      (X := TopCat.of ↥U) (∅ : Set (TopCat.of ↥U)) (k - 1) h1' h0
  -- transfer back to the absolute cochain complex
  haveI := relComplex_empty_homology_iso (TopCat.of ↥U) k
  exact subsingleton_of_iso_aux (asIso (HomologicalComplex.homologyMap
    (relIncl ℤ (TopCat.of ↥U) (∅ : Set (TopCat.of ↥U))) k)) hS

/-- **The cohomology of an open subset of `ℝ^N` vanishes in degrees `≥ N`.** -/
theorem euclidean_open_cohomology_vanishing {N : ℕ} (hN : 1 ≤ N)
    (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U) :
    ∀ k, N ≤ k →
      Subsingleton ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of ↥U)).homology k) :=
  euclidean_open_cohomology_vanishing_of_inputs hN U
    (fun m hm => euclidean_open_homology_vanishing hN U hU m hm)
    (euclidean_top_homology_free hN U hU)

end

end Work.Cohomology
