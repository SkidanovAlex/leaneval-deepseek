import Mathlib
import Submission.Work.EKLComp.ErgMax.Basic

/-!
# C4c — the set of probability measures carried by `Drho ρ` is compact

Component C4c of the frozen EKL contract maximises the entropy over the (convex, compact) set
`M = {μ : ProbabilityMeasure X₃ | μ (Drho ρ) = 1}` (with `μ` also `a₀`-invariant).  Compactness
of `M` is supplied by `ErgMax.isCompactProb_massDrho`:

* `Drho ρ` is compact (`Work.EKLContract.isCompact_Drho`: it is a closed subset of the compact
  set `Thick ρ = {λ₁ ≥ ρ}`, Mahler compactness);
* the set of probability measures of total mass one carried by a *compact* set is compact
  (Prokhorov; `MeasureTheory.isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le`),
  and being carried by `Drho ρ` is the same condition as `μ (Drho ρ) = 1`.

No topological hypothesis beyond Mahler compactness (`P_X3`) is used.
-/

namespace Work.EKLComp.ErgMax

open MeasureTheory Topology Filter
open scoped ENNReal

open Work.EKLContract

set_option linter.style.haveILetI false

noncomputable section

/-- For a probability measure `μ` and a *measurable* set `s`, `μ s = 1` is the same as
`μ sᶜ = 0` (both express that `μ` is carried by `s`). -/
theorem measure_eq_one_iff_compl_eq_zero {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    μ s = 1 ↔ μ sᶜ = 0 := by
  rw [measure_compl hs (measure_ne_top μ s), measure_univ]
  constructor
  · intro h; rw [h, tsub_self]
  · intro h
    have h1 : (1 : ℝ≥0∞) ≤ μ s := tsub_eq_zero_iff_le.mp h
    have h2 : μ s ≤ μ Set.univ := measure_mono (Set.subset_univ s)
    rw [measure_univ] at h2
    exact le_antisymm h2 h1

/-- **C4c (compactness).** The probability measures on `X₃` carried by `Drho ρ` form a weakly
compact set.  `Drho ρ` is compact by Mahler compactness, and the probability measures carried by
a compact set form a compact set by Prokhorov's theorem. -/
theorem isCompactProb_massDrho (h2 : Work.EKLContract.P_X3) {ρ : ℝ} (hρ : 0 < ρ) :
    Work.EKLComp.ErgMax.IsCompactProb {μ : MeasureTheory.Measure Work.EKLContract.X3 |
      μ (Work.EKLContract.Drho ρ) = 1} := by
  haveI : T2Space X3 := h2.1
  have hK : IsCompact (Drho ρ) := isCompact_Drho h2 hρ
  have hmeas : MeasurableSet (Drho ρ) := hK.isClosed.measurableSet
  -- Prokhorov, with the constant sequence of compact sets `Drho ρ` and `u ≡ 0`:
  have hprob : IsCompact {μ : ProbabilityMeasure X3 | ∀ n : ℕ, μ (Drho ρ)ᶜ ≤ (0 : NNReal)} := by
    simpa using isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
      (u := fun _ => 0) (K := fun _ => Drho ρ) tendsto_const_nhds (fun _ => hK)
      (Or.inr fun _ _ _ => subset_rfl)
  -- being carried by `Drho ρ` is the same as `μ (Drho ρ) = 1`
  have hset : {μ : ProbabilityMeasure X3 | (μ : Measure X3) (Drho ρ) = 1}
      = {μ : ProbabilityMeasure X3 | ∀ n : ℕ, μ (Drho ρ)ᶜ ≤ (0 : NNReal)} := by
    ext μ
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h n
      have h0 : (μ : Measure X3) (Drho ρ)ᶜ = 0 :=
        (measure_eq_one_iff_compl_eq_zero (μ : Measure X3) hmeas).mp h
      have h1 : μ (Drho ρ)ᶜ = 0 := (ProbabilityMeasure.null_iff_toMeasure_null μ _).mpr h0
      rw [h1]
    · intro h
      have h0 : μ (Drho ρ)ᶜ = 0 := le_bot_iff.mp (h 0)
      have h0' : (μ : Measure X3) (Drho ρ)ᶜ = 0 :=
        (ProbabilityMeasure.null_iff_toMeasure_null μ _).mp h0
      exact (measure_eq_one_iff_compl_eq_zero (μ : Measure X3) hmeas).mpr h0'
  rw [IsCompactProb]
  simp only [Set.mem_ofPred_eq]
  rw [hset]
  exact hprob

end

end Work.EKLComp.ErgMax
