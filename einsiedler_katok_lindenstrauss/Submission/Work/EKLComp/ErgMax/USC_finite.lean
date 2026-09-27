import Mathlib
import Submission.Work.EKLComp.ErgMax.USCDefs
import Submission.Work.EKLComp.exists_small_part

/-!
# C4c — clause (i) of `P_USC'`: uniform finiteness of the entropy

An `AtomSmall` partition `P` exists (`Work.EKLComp.exists_small_part`), and it is *fixed*
independently of `ν`.  EKL Prop 9.2 (`AtomSmallEntropy`) then gives
`ent ν a = ofReal (hPart ν a P) ≤ log |P|` for every `a`-invariant probability carried by `K`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace Work.EKLComp.ErgMax

open Work.EKLContract

noncomputable section

set_option linter.style.haveILetI false

theorem P_USC'_finite (h : ∀ (t : Fin 3 → ℝ), (∃ i j : Fin 3, t i ≠ t j) →
    ∀ (K : Set X3), IsCompact K → (∀ x ∈ K, aDiag t • x ∈ K) → AtomSmallEntropy t K)
    (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) (K : Set X3) (hK : IsCompact K)
    (hfwd : ∀ x ∈ K, aDiag t • x ∈ K) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : Measure X3, IsProbabilityMeasure ν → ν K = 1 →
      MeasurePreserving (fun x : X3 => aDiag t • x) ν ν →
      ent ν (fun x : X3 => aDiag t • x) ≤ C := by
  obtain ⟨δ, hδ, hδP⟩ := h t ht K hK hfwd
  obtain ⟨P, hPsmall, -⟩ := Work.EKLComp.exists_small_part K hK (Measure.dirac (mkX 1)) hδ
  refine ⟨ENNReal.ofReal (Real.log (P.n : ℝ)), ENNReal.ofReal_lt_top, ?_⟩
  intro ν hprob hKν hmp
  haveI := hprob
  rw [hδP P hPsmall ν hprob hKν hmp]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : hPart ν (fun x : X3 => aDiag t • x) P ≤ Hfam ν P.parts := hPart_le_Hfam ν _ P
  have h2 : Hfam ν P.parts ≤ Real.log (P.n : ℝ) := by
    have := Work.EKLComp.Core.Hfam_le_log_card ν (isMPart_parts P)
    simpa using this
  linarith

end

end Work.EKLComp.ErgMax
