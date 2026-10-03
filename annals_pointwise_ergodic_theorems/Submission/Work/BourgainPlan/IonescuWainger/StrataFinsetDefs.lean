import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.charSum_sigmaSubAFinset

/-!
# Tao's strata `Σ_A = Σ_{⊆ A} \ ⋃_{B ⊊ A} Σ_{⊆ B}` as `Finset`s of the circle

`ArcFinsetDefs.lean` records the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]` as `sigmaSubAFinset A` and the
points of *exact* denominator `Q_A` as `sigmaAFinset A`.  Tao's strata `Σ_A`
(arXiv:2008.05066, Definition `major-arc`) are neither: they are

`Σ_A = Σ_{⊆ A} \ ⋃_{B ⊊ A} Σ_{⊆ B}`,

the torsion subgroup minus all strictly smaller torsion subgroups `𝕋[Q_B]`, `B ⊊ A`.  For composite
elements of `S` this is strictly larger than `sigmaAFinset A`, and it is the family that partitions
`Σ_{≤ k}` (which is what the coverage step of `ortho-apply` and the inclusion–exclusion step of the
`p = ∞` endpoint need).

This file defines `sigmaStrataFinset A` and its elementary properties.  The companion file
`arcSymbol_strata_incl_excl` proves the Möbius/inclusion–exclusion identity
`1_{Σ_A} = ∑_{B ⊆ A} (-1)^{|A| - |B|} 1_{Σ_{⊆ B}}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- **Tao's stratum `Σ_A`** as a `Finset` of the circle: the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]`
with all strictly smaller torsion subgroups `Σ_{⊆ B}`, `B ⊊ A`, removed. -/
noncomputable def sigmaStrataFinset (A : Finset ℕ) : Finset Circle :=
  sigmaSubAFinset A \ (A.powerset.erase A).biUnion sigmaSubAFinset

/-- Membership in the stratum. -/
theorem mem_sigmaStrataFinset {A : Finset ℕ} {β : Circle} :
    β ∈ sigmaStrataFinset A ↔
      β ∈ sigmaSubAFinset A ∧ ∀ B ∈ A.powerset.erase A, β ∉ sigmaSubAFinset B := by
  classical
  rw [sigmaStrataFinset, Finset.mem_sdiff, Finset.mem_biUnion]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun B hB hβ => h2 ⟨B, hB, hβ⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun ⟨B, hB, hβ⟩ => h2 B hB hβ⟩

/-- The stratum is contained in the torsion subgroup. -/
theorem sigmaStrataFinset_subset_sigmaSubAFinset (A : Finset ℕ) :
    sigmaStrataFinset A ⊆ sigmaSubAFinset A := by
  intro β hβ
  exact (mem_sigmaStrataFinset.mp hβ).1

/-- A point of a *strictly smaller* torsion subgroup is not in the stratum. -/
theorem not_mem_sigmaStrataFinset_of_mem_sigmaSubAFinset {A B : Finset ℕ}
    (hBA : B ⊆ A) (hne : B ≠ A) {β : Circle} (hβ : β ∈ sigmaSubAFinset B) :
    β ∉ sigmaStrataFinset A := by
  classical
  intro hmem
  exact (mem_sigmaStrataFinset.mp hmem).2 B (Finset.mem_erase.mpr ⟨hne, by
    rw [Finset.mem_powerset]; exact hBA⟩) hβ

/-- The strata of the singletons: for a single prime `q`, `Σ_{{q}}` is `𝕋[q]` minus `{0}`. -/
theorem sigmaStrataFinset_singleton_subset (q : ℕ) :
    sigmaStrataFinset {q} ⊆ sigmaSubAFinset {q} :=
  sigmaStrataFinset_subset_sigmaSubAFinset {q}

end Work.BourgainPlan.IonescuWainger
