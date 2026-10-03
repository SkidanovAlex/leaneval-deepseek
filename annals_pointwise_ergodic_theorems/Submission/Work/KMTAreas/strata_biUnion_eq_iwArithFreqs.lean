/-
# The biUnion of the admissible strata of `S_l` is `(ℚ/ℤ)_{≤l}`

Let `ρ ∈ (0,1]`, `l > C⁰_ρ` and let

  `S_l = iwSL ρ l = {Q_0^{(l)}} ∪ {p^{D_ρ} : p ∈ (N_0^{(l)}, 2^l] prime}`

be the "Tao denominator set" of Appendix A of Krause–Mirek–Tao.  A subset `A ⊆ S_l` of
cardinality at most `D_ρ + 1` is called *admissible* when

  `Q_0^{(l)} ∈ A  or  #A ≤ D_ρ`.

The main theorem of `mem_sigmaStrataFinset_subset_iwArithFreqs` says that Tao's stratum `Σ_A`
of an admissible `A` lies in the Ionescu–Wainger arithmetic frequency set
`(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l`, and that no other subset of `S_l` of cardinality at most
`D_ρ + 1` has this property:

  `Σ_A ⊆ (ℚ/ℤ)_{≤l}  ↔  Q_0^{(l)} ∈ A ∨ #A ≤ D_ρ`.

This file upgrades that pointwise characterisation to the identity of `Finset`s

  `⋃_{A admissible} Σ_A = (ℚ/ℤ)_{≤l}`

(Tao, arXiv:2008.05066, `major-arc`/`ortho-apply`: the strata of an admissible family cover the
major arc set; here the major arc set is the IW frequency set itself).

The two halves:

* `⊆` is immediate from the characterisation above;
* `⊇` combines the arithmetic witness `exists_iwSL_witness_sigmaSubAFinset` (every IW frequency
  is a `Q_A`-torsion point for some admissible `A` containing `Q_0^{(l)}`) with the abstract
  minimality lemma `exists_subset_mem_sigmaStrataFinset` (a point of a torsion subgroup
  `Σ_{⊆ A} = 𝕋[Q_A]` lies in one of the strata `Σ_B`, `B ⊆ A`).  The minimal `B ⊆ A` is
  admissible: if it misses `Q_0^{(l)}` then `#B ≤ #A - 1 ≤ D_ρ`.
-/
import Mathlib
import Submission.Work.KMTAreas.mem_sigmaStrataFinset_subset_iwArithFreqs
import Submission.Work.KMTAreas.exists_iwSL_witness_sigmaSubAFinset
import Submission.Work.KMTAreas.exists_subset_mem_sigmaStrataFinset

namespace Work.KMTAreas

/-- **The strata of the admissible subsets of `S_l` cover exactly `(ℚ/ℤ)_{≤l}`.**

For `ρ ∈ (0,1]` and `l > C⁰_ρ`, the union of Tao's strata `Σ_A` over the subsets
`A ⊆ S_l = iwSL ρ l` with `#A ≤ D_ρ + 1` and (`Q_0^{(l)} ∈ A` or `#A ≤ D_ρ`) is the
Ionescu–Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l`. -/
theorem strata_biUnion_eq_iwArithFreqs (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ}
    (hl : Work.Analysis.IonescuWainger.iwC0 ρ < l) :
    (((Work.KMTAreas.iwSL ρ l).powerset.filter
        (fun A => A.card ≤ Work.Analysis.IonescuWainger.iwD ρ + 1)).filter
        (fun A => Work.Analysis.IonescuWainger.iwQ0 ρ l ∈ A ∨
          A.card ≤ Work.Analysis.IonescuWainger.iwD ρ)).biUnion
        Work.BourgainPlan.IonescuWainger.sigmaStrataFinset
      = Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  classical
  apply Finset.Subset.antisymm
  · -- `⊆`: every stratum of an admissible set lies in `(ℚ/ℤ)_{≤l}`
    intro β hβ
    rw [Finset.mem_biUnion] at hβ
    obtain ⟨A, hA, hβA⟩ := hβ
    rw [Finset.mem_filter] at hA
    obtain ⟨hA1, hcond⟩ := hA
    rw [Finset.mem_filter, Finset.mem_powerset] at hA1
    obtain ⟨hAsub, hAcard⟩ := hA1
    exact (mem_sigmaStrataFinset_subset_iwArithFreqs ρ hρ hρ1 hl
      (by simpa only [iwSL] using hAsub) hAcard).mpr hcond hβA
  · -- `⊇`: an admissible torsion subgroup already contains a stratum through the point
    intro β hβ
    obtain ⟨A, hAsub, hQ0mem, hAcard, hβA⟩ :=
      exists_iwSL_witness_sigmaSubAFinset ρ hρ hρ1 hl hβ
    obtain ⟨B, hBA, hβB⟩ := exists_subset_mem_sigmaStrataFinset hβA
    rw [Finset.mem_biUnion]
    refine ⟨B, ?_, hβB⟩
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨hBA.trans hAsub, le_trans (Finset.card_le_card hBA) hAcard⟩, ?_⟩
    by_cases hQ0B : Work.Analysis.IonescuWainger.iwQ0 ρ l ∈ B
    · exact Or.inl hQ0B
    · -- `B` misses `Q_0^{(l)}`, so `#B ≤ #(A \ {Q_0^{(l)}}) = #A - 1 ≤ D_ρ`
      refine Or.inr ?_
      have hsub : B ⊆ A.erase (Work.Analysis.IonescuWainger.iwQ0 ρ l) := by
        intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hQ0B (h ▸ hx), hBA hx⟩
      have h1 : B.card ≤ (A.erase (Work.Analysis.IonescuWainger.iwQ0 ρ l)).card :=
        Finset.card_le_card hsub
      have h2 : (A.erase (Work.Analysis.IonescuWainger.iwQ0 ρ l)).card = A.card - 1 :=
        Finset.card_erase_of_mem hQ0mem
      omega

end Work.KMTAreas
