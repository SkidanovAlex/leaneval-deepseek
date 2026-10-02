import Mathlib
import Submission.Work.PTGeometric.SourceConstruction
import Submission.Work.PTGeometric.RegionManifoldNC

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: a smooth defining function with prescribed vanishing and saturation

The last mile of the source construction needs a smooth function `ρ ≥ 0` on the half-space that
vanishes **exactly** on a compact closed set `Z` (the preimage of the core of the Thom space under
the null-homotopy), is `≥ 1` on a closed set `T` disjoint from `Z`, and is `≥ 1` outside a compact
set `K` (so that `ρ` is `1` at infinity).  This is the smooth Urysohn lemma with two extra
features: the zero set is *exactly* `Z`, and the function is *eventually* `1`.

## Construction

`exists_compact_superset hZc` (weak local compactness of the half-space, from the fact that the
half-space is a closed subset of a finite-dimensional Euclidean space) produces a compact `K` with
`Z ⊆ interior K`.  Then `T ∪ (interior K)ᶜ` is closed and disjoint from `Z`, and Mathlib's
`exists_contMDiff_zero_iff_one_iff_of_isClosed` produces `f` with `f = 0` exactly on `Z` and `f = 1`
exactly on `T ∪ (interior K)ᶜ`; since `Kᶜ ⊆ (interior K)ᶜ`, this `f` is `1` off `K`.

## Main results

* `Work.PTGeometric.exists_sourceDefiningFunction`
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped Manifold

namespace Work.PTGeometric

noncomputable section

/-- **A smooth defining function of a compact set, saturated off a compact set.**

For a closed compact `Z` and a closed `T` disjoint from `Z` in the half-space `EuclideanHalfSpace N`
(with `N ≠ 0`) there is a `C^∞` function `ρ` with `0 ≤ ρ`, `ρ = 0 ↔ x ∈ Z`, `ρ ≥ 1` on `T`, and
`ρ ≥ 1` outside a compact set `K`.  (The last two conditions together say that `ρ = 1` exactly on a
closed set containing `T` and the complement of `K`.) -/
theorem exists_sourceDefiningFunction (N : ℕ) [NeZero N] (Z T : Set (EuclideanHalfSpace N)) (hZcl : IsClosed Z) (hZc : IsCompact Z) (hTcl : IsClosed T) (hd : Disjoint Z T) : ∃ ρ : EuclideanHalfSpace N → ℝ, ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ (∀ x, 0 ≤ ρ x) ∧ (∀ x, ρ x = 0 ↔ x ∈ Z) ∧ (∀ x ∈ T, 1 ≤ ρ x) ∧ (∃ K : Set (EuclideanHalfSpace N), IsCompact K ∧ ∀ x, x ∉ K → 1 ≤ ρ x) := by
  -- The half-space is a closed subset of a finite-dimensional Euclidean space, hence weakly
  -- locally compact and σ-compact, and it is Hausdorff.
  have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin N) | 0 ≤ x 0} :=
    isClosed_le continuous_const (by fun_prop)
  haveI : WeaklyLocallyCompactSpace (EuclideanHalfSpace N) := by
    change WeaklyLocallyCompactSpace {x : EuclideanSpace ℝ (Fin N) // 0 ≤ x 0}
    exact hclosed.weaklyLocallyCompactSpace
  haveI : SigmaCompactSpace (EuclideanHalfSpace N) := by
    change SigmaCompactSpace {x : EuclideanSpace ℝ (Fin N) // 0 ≤ x 0}
    exact hclosed.sigmaCompactSpace
  haveI : T2Space (EuclideanHalfSpace N) := by
    change T2Space {x : EuclideanSpace ℝ (Fin N) // 0 ≤ x 0}
    infer_instance
  -- A compact set containing `Z` in its interior.
  obtain ⟨K, hKc, hZK⟩ := exists_compact_superset (X := EuclideanHalfSpace N) hZc
  -- `T ∪ (interior K)ᶜ` is closed and disjoint from `Z`.
  have ht : IsClosed (T ∪ (interior K)ᶜ) := hTcl.union isOpen_interior.isClosed_compl
  have hd' : Disjoint Z (T ∪ (interior K)ᶜ) := by
    rw [Set.disjoint_left]
    intro x hxZ hx
    rcases hx with hxT | hxK
    · exact Set.disjoint_left.mp hd hxZ hxT
    · exact hxK (hZK hxZ)
  obtain ⟨f, hf, hrange, h0, h1⟩ :=
    exists_contMDiff_zero_iff_one_iff_of_isClosed (modelWithCornersEuclideanHalfSpace N) hZcl ht hd'
  refine ⟨f, hf, ?_, ?_, ?_, ?_⟩
  · intro x; exact (hrange (Set.mem_range_self x)).1
  · intro x; exact (h0 x).symm
  · intro x hx
    rw [(h1 x).mp (Or.inl hx)]
  · refine ⟨K, hKc, ?_⟩
    intro x hx
    have hxt : x ∈ (T ∪ (interior K)ᶜ) := Or.inr (fun hxint => hx (interior_subset hxint))
    rw [(h1 x).mp hxt]

end

end Work.PTGeometric
