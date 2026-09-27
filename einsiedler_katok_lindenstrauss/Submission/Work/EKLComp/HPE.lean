import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.partSigmaFam_joinSets

/-!
# C3 — the conditional-entropy formula for `hPart`: supporting lemmas
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.EKLComp.Core

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

theorem partSigmaFam_comap (T : X → X) {ι : Type*} (A : ι → Set X) :
    partSigmaFam (fun i => T ⁻¹' A i) = MeasurableSpace.comap T (partSigmaFam A) := by
  rw [partSigmaFam, partSigmaFam, MeasurableSpace.comap_generateFrom]
  congr 1
  ext S
  simp only [Set.mem_image, Set.mem_range, Set.mem_preimage]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨A i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨S, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩

/-- The σ-algebra `⋁_{k<N} T^{-(k+1)}(σ P)`. -/
def JN (T : X → X) (P : FinPart X) (N : ℕ) : MeasurableSpace X :=
  ⨆ k : Fin N, MeasurableSpace.comap (T^[(k:ℕ)+1]) (partSigma P)

theorem partSigmaFam_shift (T : X → X) (P : FinPart X) (N : ℕ) :
    partSigmaFam (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v) = JN T P N := by
  have h1 : partSigmaFam (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v)
      = MeasurableSpace.comap T (partSigmaFam (joinSets T P N)) := partSigmaFam_comap T _
  have h2 : partSigmaFam (joinSets T P N)
      = ⨆ k : Fin N, MeasurableSpace.comap (T^[(k:ℕ)]) (partSigma P) :=
    partSigmaFam_joinSets T P N
  rw [h1, h2, JN, MeasurableSpace.comap_iSup]
  refine iSup_congr fun k => ?_
  rw [MeasurableSpace.comap_comp]
  congr 1

theorem joinSets_cons (T : X → X) (P : FinPart X) (N : ℕ)
    (i : Fin P.n) (v : Fin N → Fin P.n) :
    joinSets T P (N+1) (Fin.cons i v) = T ⁻¹' joinSets T P N v ∩ P.parts i := by
  ext x
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage, Set.mem_inter_iff]
  rw [Fin.forall_fin_succ]
  constructor
  · rintro ⟨h0, hs⟩
    exact ⟨fun j => by simpa [Fin.cons_succ, Function.iterate_succ] using hs j,
      by simpa [Fin.cons_zero] using h0⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa [Fin.cons_zero] using h2,
      fun j => by simpa [Fin.cons_succ, Function.iterate_succ] using h1 j⟩

theorem Hfam_shift (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v) = Hfam μ (joinSets T P N) := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [MeasurePreserving.measure_preimage hmp
    (joinSets_measurable hmp.measurable P N v).nullMeasurableSet]

/-- `(Fin N → α) × α ≃ (Fin (N+1) → α)`, `(v, i) ↦` the tuple with `i` first. -/
def consEquiv (α : Type*) (N : ℕ) : (Fin N → α) × α ≃ (Fin (N+1) → α) where
  toFun q := Fin.cons q.2 q.1
  invFun w := (fun j => w (Fin.succ j), w 0)
  left_inv := by
    rintro ⟨v, i⟩
    simp [Fin.cons_zero, Fin.cons_succ]
  right_inv := by
    intro w
    exact Fin.cons_self_tail w

theorem iSup_JN (T : X → X) (P : FinPart X) :
    (⨆ N : ℕ, JN T P N) = ⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (partSigma P) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun N => iSup_le fun k => ?_
    exact le_iSup (fun n : ℕ => MeasurableSpace.comap (T^[n+1]) (partSigma P)) (k:ℕ)
  · refine iSup_le fun n => ?_
    refine le_trans ?_ (le_iSup (fun N : ℕ => JN T P N) (n+1))
    exact le_iSup (fun k : Fin (n+1) =>
      MeasurableSpace.comap (T^[(k:ℕ)+1]) (partSigma P)) ⟨n, by omega⟩

end Work.EKLComp.Core
