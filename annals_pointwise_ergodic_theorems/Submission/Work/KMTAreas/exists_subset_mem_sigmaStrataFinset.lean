import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs

/-!
# The strata below a torsion subgroup cover it

Tao's strata `Σ_A = sigmaStrataFinset A` are the sets `𝕋[Q_A] \ ⋃_{B ⊊ A} 𝕋[Q_B]` of points of the
circle of *exact* denominator `Q_A`.  Their defining property, used every time the strata are used
as a partition of a torsion subgroup `Σ_{⊆ A} = sigmaSubAFinset A` (e.g. to split
`Op_{ψ; Σ_{⊆A}}` into the `Op_{ψ; Σ_B}`, `B ⊆ A`), is that

  **every point of `Σ_{⊆ A}` lies in a stratum `Σ_B` for some `B ⊆ A`.**

This is purely Boolean: taking `B ⊆ A` of *minimal cardinality* among the subsets `C ⊆ A` with
`β ∈ Σ_{⊆ C}`, any proper subset `C ⊊ B` has strictly smaller cardinality, hence cannot contain
`β`; so `β ∈ Σ_B`.  No arithmetic (coprimality, `≥ 2`) is needed.
-/

namespace Work.KMTAreas

open Work.BourgainPlan.IonescuWainger

theorem exists_subset_mem_sigmaStrataFinset {A : Finset ℕ}
    {β : Work.BourgainPlan.IonescuWainger.Circle}
    (hβ : β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A) :
    ∃ B : Finset ℕ, B ⊆ A ∧
      β ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset B := by
  classical
  -- the family of subsets of `A` whose torsion subgroup contains `β`
  set T : Finset (Finset ℕ) := A.powerset.filter (fun C => β ∈ sigmaSubAFinset C) with hT
  have hTne : T.Nonempty :=
    ⟨A, by rw [hT]; exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (le_refl A), hβ⟩⟩
  -- pick an element of minimal cardinality
  obtain ⟨B, hBT, hmin⟩ := Finset.exists_min_image T (fun C => C.card) hTne
  rw [hT, Finset.mem_filter] at hBT
  obtain ⟨hBsub, hβB⟩ := hBT
  refine ⟨B, Finset.mem_powerset.mp hBsub, ?_⟩
  rw [mem_sigmaStrataFinset]
  refine ⟨hβB, ?_⟩
  -- no *proper* subset of `B` has `β` in its torsion subgroup
  intro C hC hβC
  rw [Finset.mem_erase, Finset.mem_powerset] at hC
  obtain ⟨hCne, hCsub⟩ := hC
  have hCT : C ∈ T := by
    rw [hT, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hCsub.trans (Finset.mem_powerset.mp hBsub), hβC⟩
  have hle := hmin C hCT
  have hlt : C.card < B.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hCsub, hCne⟩)
  omega

end Work.KMTAreas
