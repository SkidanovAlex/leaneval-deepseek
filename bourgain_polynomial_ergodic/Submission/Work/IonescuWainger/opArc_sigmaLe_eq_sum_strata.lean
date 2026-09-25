import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl
import Submission.Work.BourgainPlan.IonescuWainger.opArc_eq_sum_singletons
import Submission.Work.BourgainPlan.IonescuWainger.opArc_l2_endpoint_strata
import Submission.Work.BourgainPlan.IonescuWainger.StrataArcArith

namespace Work.IonescuWainger

open Finset
open scoped BigOperators
open Work.BourgainPlan.IonescuWainger (sigmaLeFinset sigmaStrataFinset sigmaSubAFinset)
open Work.BourgainPlan.IonescuWainger (opArc opArc_eq_sum_singletons)

/-! ## The strata partition `Σ_{≤ k}`

The two structural facts behind `opArc_sigmaLe_eq_sum_strata` are that the strata
`Σ_A = sigmaStrataFinset A`, `A ∈ binom(S, ≤ k)`, *cover* `Σ_{≤ k} = sigmaLeFinset S k` and are
*pairwise disjoint* (the latter is `circle_strata_disjoint` of `opArc_l2_endpoint_strata`).  The
covering is purely Boolean — a minimality argument on the index sets — and needs no arithmetic.
-/

/-- **The strata cover `Σ_{≤ k}`.**  A point `β` of the circle lies in the union of the torsion
subgroups `Σ_{⊆ A} = 𝕋[Q_A]` over the index sets `A ⊆ S` with `A.card ≤ k` if and only if it lies
in one of the strata `Σ_A = sigmaStrataFinset A` with `A ⊆ S`, `A.card ≤ k`.

The proof is a minimality argument on the finite family of index sets `A ⊆ S`, `A.card ≤ k` with
`β ∈ Σ_{⊆ A}` (as in the `ZMod` version `strata_cover`): a member of minimal cardinality satisfies
the stratum condition, since the stratum condition only excludes *proper* subsets, which have
strictly smaller cardinality. -/
lemma mem_sigmaLeFinset_iff_exists_mem_sigmaStrataFinset (S : Finset ℕ) (k : ℕ)
    (β : Work.BourgainPlan.IonescuWainger.Circle) :
    β ∈ sigmaLeFinset S k ↔
      ∃ A ∈ S.powerset.filter (fun A => A.card ≤ k), β ∈ sigmaStrataFinset A := by
  classical
  constructor
  · intro hβ
    rw [sigmaLeFinset, Finset.mem_biUnion] at hβ
    obtain ⟨A₀, hA₀, hβA₀⟩ := hβ
    set T : Finset (Finset ℕ) :=
      (S.powerset.filter (fun A => A.card ≤ k)).filter (fun A => β ∈ sigmaSubAFinset A) with hT
    have hTne : T.Nonempty := ⟨A₀, by rw [hT]; exact Finset.mem_filter.mpr ⟨hA₀, hβA₀⟩⟩
    obtain ⟨A, hAT, hmin⟩ := Finset.exists_min_image T (fun A => A.card) hTne
    rw [hT, Finset.mem_filter] at hAT
    obtain ⟨hAF, hβA⟩ := hAT
    refine ⟨A, hAF, ?_⟩
    rw [Work.BourgainPlan.IonescuWainger.mem_sigmaStrataFinset]
    refine ⟨hβA, ?_⟩
    intro B hB hβB
    rw [Finset.mem_erase, Finset.mem_powerset] at hB
    obtain ⟨hBne, hBsub⟩ := hB
    have hBF : B ∈ S.powerset.filter (fun A => A.card ≤ k) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hBsub.trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hAF).1),
        le_trans (Finset.card_le_card hBsub) (Finset.mem_filter.mp hAF).2⟩
    have hBT : B ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hBF, hβB⟩
    have hle := hmin B hBT
    have hlt : B.card < A.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBsub, hBne⟩)
    omega
  · rintro ⟨A, hA, hβ⟩
    rw [sigmaLeFinset, Finset.mem_biUnion]
    exact ⟨A, hA, Work.BourgainPlan.IonescuWainger.sigmaStrataFinset_subset_sigmaSubAFinset A hβ⟩

/-- **The strata of `binom(S, ≤ k)` partition `Σ_{≤ k}`** (the covering half, in `Finset` form). -/
lemma biUnion_sigmaStrataFinset_eq_sigmaLeFinset (S : Finset ℕ) (k : ℕ) :
    (S.powerset.filter (fun A => A.card ≤ k)).biUnion sigmaStrataFinset = sigmaLeFinset S k := by
  ext β
  rw [Finset.mem_biUnion]
  exact (mem_sigmaLeFinset_iff_exists_mem_sigmaStrataFinset S k β).symm

/-- **The strata of distinct subsets of `S` are disjoint** (in the `Set.PairwiseDisjoint` form
required by `Finset.sum_biUnion`), for `S` a finite set of pairwise coprime integers `≥ 2`. -/
lemma pairwiseDisjoint_sigmaStrataFinset (S : Finset ℕ) (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (k : ℕ) :
    (↑(S.powerset.filter (fun A => A.card ≤ k)) : Set (Finset ℕ)).PairwiseDisjoint
      sigmaStrataFinset := by
  intro A hA B hB hAB
  change Disjoint (sigmaStrataFinset A) (sigmaStrataFinset B)
  rw [Finset.disjoint_left]
  intro β hβA hβB
  exact hAB (Work.BourgainPlan.IonescuWainger.circle_strata_disjoint h2 hS
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1)
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1) hβA hβB)

-- Design note: A6_ASSEMBLY_GUIDE.md; this is the identity between Tao's two formulations of `main` (the union form `Op_{ψ;Σ_{≤k}}` and the unsigned strata sum `Σ_A Op_{ψ;Σ_A}`, the strata being a partition).
theorem opArc_sigmaLe_eq_sum_strata {S : Finset ℕ} (h2S : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) {k : ℕ}
    (ψ : Work.BourgainPlan.IonescuWainger.Circle → ℂ)
    (hψ : MeasureTheory.MemLp ψ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Work.BourgainPlan.IonescuWainger.opArc ψ hψ
        (Work.BourgainPlan.IonescuWainger.sigmaLeFinset S k) f hf
      = ∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          Work.BourgainPlan.IonescuWainger.opArc ψ hψ
            (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf := by
  classical
  -- Both sides are sums of the single-frequency operators `Op_{ψ;{β}}`: the left one over
  -- `Σ_{≤ k}`, the right one over the (disjoint) strata.
  have hmain : (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        Work.BourgainPlan.IonescuWainger.opArc ψ hψ
          (Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A) f hf)
      = ∑ β ∈ Work.BourgainPlan.IonescuWainger.sigmaLeFinset S k,
          Work.BourgainPlan.IonescuWainger.opArc ψ hψ {β} f hf := by
    rw [Finset.sum_congr rfl
      (fun A _ => opArc_eq_sum_singletons ψ hψ (sigmaStrataFinset A) f hf)]
    rw [← Finset.sum_biUnion (f := fun β => opArc ψ hψ {β} f hf)
        (pairwiseDisjoint_sigmaStrataFinset S h2S hS k),
      biUnion_sigmaStrataFinset_eq_sigmaLeFinset]
  rw [hmain, opArc_eq_sum_singletons ψ hψ (sigmaLeFinset S k) f hf]

end Work.IonescuWainger
