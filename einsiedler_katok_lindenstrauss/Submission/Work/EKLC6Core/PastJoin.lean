import Mathlib
import Submission.Work.EKLComp.Hcond

/-!
# `EKLC6Core.PastJoin` — the "punctured" join `⋁_{k=1}^{N} T^{-k}P` and the past σ-algebra

For the Kolmogorov–Sinai identity `h_μ(T,P) = H_μ(P | ⋁_{n≥1} T^{-n}P)` one must compare the
conditional entropy of `P` given the *punctured* join

  `⋁_{k=1}^{N} T^{-k}P = T^{-1}(⋁_{k<N} T^{-k}P)`

with the difference `Hfam μ (⋁_{k<N+1} T^{-k}P) - Hfam μ (⋁_{k<N} T^{-k}P)` of Shannon entropies.
This module fixes the vocabulary:

* `shJoin T P N` — the family of atoms of `⋁_{k=1}^{N} T^{-k}P`, i.e. `T ⁻¹' joinSets T P N w`;
* `shiftSigma T P N` — its σ-algebra (`partSigmaFam (shJoin T P N)`);
* `pastSigmaShift T P` — the σ-algebra `⋁_{k:ℕ} T^{-(k+1)}(partSigma P)` of the statement.

The lemmas proved here are the elementary ones: the atoms are the expected intersections of
preimages, `shiftSigma T P N ≤ pastSigmaShift T P`, and the two `Hfam` computations (invariance under
the measure-preserving `T⁻¹`, and the splitting of `P ∨ shJoin T P N` as `joinSets T P (N+1)`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract
open Work.EKLComp.Core

variable {X : Type*} [mX : MeasurableSpace X]

/-- The atoms of the punctured join `⋁_{k=1}^{N} T^{-k}P = T^{-1}(⋁_{k<N} T^{-k}P)`. -/
def shJoin (T : X → X) (P : FinPart X) (N : ℕ) : (Fin N → Fin P.n) → Set X :=
  fun w => T ⁻¹' joinSets T P N w

/-- The σ-algebra `⋁_{k=1}^{N} T^{-k}(partSigma P)` of the punctured join. -/
def shiftSigma (T : X → X) (P : FinPart X) (N : ℕ) : MeasurableSpace X :=
  partSigmaFam (shJoin T P N)

/-- The past σ-algebra `⋁_{k:ℕ} T^{-(k+1)}(partSigma P)` of the statement. -/
def pastSigmaShift (T : X → X) (P : FinPart X) : MeasurableSpace X :=
  ⨆ k : ℕ, MeasurableSpace.comap (T^[k+1]) (partSigma P)

@[simp] theorem shJoin_apply (T : X → X) (P : FinPart X) (N : ℕ)
    (w : Fin N → Fin P.n) : shJoin T P N w = T ⁻¹' joinSets T P N w := rfl

/-- The atom `shJoin T P N w` is the intersection `⋂_{k<N} T^{-(k+1)} (P.parts (w k))`. -/
theorem shJoin_eq_iInter (T : X → X) (P : FinPart X) (N : ℕ) (w : Fin N → Fin P.n) :
    shJoin T P N w = ⋂ k : Fin N, (T^[(k : ℕ) + 1]) ⁻¹' P.parts (w k) := by
  ext x
  simp only [shJoin, joinSets, Set.mem_preimage, Set.mem_iInter]
  exact ⟨fun h k => h k, fun h k => h k⟩

/-- The punctured join is a measurable partition when `T` is measurable. -/
theorem shJoin_isMPart {T : X → X} (hT : Measurable T) (P : FinPart X) (N : ℕ) :
    IsMPart (shJoin T P N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact (joinSets_measurable hT P N w).preimage hT
  · intro u v huv
    refine Set.disjoint_left.mpr fun x hx hy => ?_
    exact Set.disjoint_left.mp (joinSets_disjoint T P N huv) hx hy
  · simp only [shJoin]
    rw [← Set.preimage_iUnion, joinSets_iUnion, Set.preimage_univ]

/-- `⋁_{k=1}^{N}T^{-k}(partSigma P)` is contained in the past σ-algebra. -/
theorem shiftSigma_le_pastSigma {T : X → X} (hT : Measurable T) (P : FinPart X) (N : ℕ) :
    shiftSigma T P N ≤ pastSigmaShift T P := by
  unfold shiftSigma pastSigmaShift
  refine MeasurableSpace.generateFrom_le fun S hS => ?_
  obtain ⟨w, rfl⟩ := hS
  rw [shJoin_eq_iInter]
  refine MeasurableSet.iInter fun k => ?_
  refine le_iSup (fun k : ℕ => MeasurableSpace.comap (T^[k+1]) (partSigma P)) ((k : ℕ)) _ ?_
  exact ⟨P.parts (w k), MeasurableSpace.measurableSet_generateFrom ⟨w k, rfl⟩, rfl⟩

/-- `Hfam` of the punctured join only sees the measures of `joinSets`, by invariance of `μ`. -/
theorem Hfam_shJoin_eq (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (shJoin T P N) = Hfam μ (joinSets T P N) := by
  have hT : Measurable T := hmp.measurable
  simp only [Hfam, shJoin]
  exact Finset.sum_congr rfl fun w _ =>
    congrArg Real.negMulLog (congrArg ENNReal.toReal
      (hmp.measure_preimage (joinSets_measurable hT P N w).nullMeasurableSet))

/-- The equivalence `Fin n × (Fin N → Fin n) ≃ (Fin (N+1) → Fin n)` given by `Fin.cons`. -/
def consEquiv (N n : ℕ) : (Fin n × (Fin N → Fin n)) ≃ (Fin (N+1) → Fin n) where
  toFun p := Fin.cons p.1 p.2
  invFun v := (v 0, fun j => v j.succ)
  left_inv p := by simp
  right_inv v := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp

@[simp] theorem consEquiv_apply' (N n : ℕ) (p : Fin n × (Fin N → Fin n)) :
    consEquiv N n p = Fin.cons p.1 p.2 := rfl

/-- Splitting an atom of `⋁_{k<N+1}T^{-k}P` at time `0`. -/
theorem parts_inter_shJoin (T : X → X) (P : FinPart X) (N : ℕ)
    (i : Fin P.n) (w : Fin N → Fin P.n) :
    P.parts i ∩ shJoin T P N w = joinSets T P (N+1) (Fin.cons i w) := by
  ext x
  simp only [shJoin, joinSets, Set.mem_preimage, Set.mem_iInter, Set.mem_inter_iff,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
  exact ⟨fun h => ⟨by simpa using h.1, fun j => h.2 j⟩,
    fun h => ⟨by simpa using h.1, fun j => h.2 j⟩⟩

/-- `Hfam` of the join of `P` with the punctured join `⋁_{k=1}^{N}T^{-k}P` is the entropy of the
full join `⋁_{k<N+1}T^{-k}P`. -/
theorem Hfam_parts_inter_shJoin (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (P : FinPart X) (N : ℕ) :
    Hfam μ (fun p : Fin P.n × (Fin N → Fin P.n) => P.parts p.1 ∩ shJoin T P N p.2) =
      Hfam μ (joinSets T P (N+1)) := by
  rw [← Hfam_equiv μ (consEquiv N P.n) (joinSets T P (N+1))]
  simp only [Hfam, consEquiv_apply']
  exact Finset.sum_congr rfl fun p _ => by rw [parts_inter_shJoin]

/-- The `0`-fold join is the trivial partition, hence has zero entropy. -/
theorem Hfam_joinSets_zero (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (P : FinPart X) : Hfam μ (joinSets T P 0) = 0 := by
  simp only [Hfam]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [joinSets_zero, measure_univ, ENNReal.toReal_one, Real.negMulLog_one]

end Work.EKLC6Core
