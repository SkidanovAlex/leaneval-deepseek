import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.cutHDefs
import Submission.Work.EKLC6Core.measure_iInter_iUnion_exp_eq_zero
import Submission.Work.EKLComp.LeafDefs

namespace Work.EKLC6Core

open MeasureTheory Set
open scoped ENNReal

/-- **The orbit eventually avoids the thin shells of the cut.**  The shells `shellThin S η` have
`μ`-measure `O η` (the thin-boundary fields of `CutData`), so the pullbacks of
`shellThin S (D νⁿ)` along the orbit of the diagonal contraction have measure `O (νⁿ)`; as
`ν < 1` the first Borel–Cantelli lemma gives that a.e. point enters them only finitely often. -/
theorem ae_deep_avoid {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3} {ε : ℝ}
    (S : Work.EKLC6Core.CutData μ U ε) {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {D ν : ℝ} (hD : 0 < D) (hν0 : 0 < ν) (hν1 : ν < 1) :
    ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) x ∉
        Work.EKLC6Core.shellThin S (D * ν ^ n) := by
  classical
  obtain ⟨C, hCpos, hthin⟩ := shellThin_bound S
  -- rewrite the geometric rate `νⁿ` as an exponential rate `exp (-(β n))`
  set β : ℝ := -Real.log ν with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]; exact neg_pos.mpr (Real.log_neg hν0 hν1)
  have hexp : ∀ n : ℕ, Real.exp (-(β * n)) = ν ^ n := by
    intro n
    rw [hβdef, show -((-Real.log ν) * (n : ℝ)) = (n : ℝ) * Real.log ν by ring,
      Real.exp_nat_mul, Real.exp_log hν0]
  -- the `n`-th pullback of the shell has measure at most `C D νⁿ`
  have hbound : ∀ n : ℕ,
      μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
          shellThin S (D * ν ^ n))
        ≤ ENNReal.ofReal (C * D * Real.exp (-(β * n))) := by
    intro n
    have hDν : 0 < D * ν ^ n := mul_pos hD (pow_pos hν0 n)
    have hle := Measure.le_map_apply (μ := μ)
      (((hmp.iterate n).measurable).aemeasurable) (shellThin S (D * ν ^ n))
    rw [(hmp.iterate n).map_eq] at hle
    calc μ (((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
            shellThin S (D * ν ^ n))
        ≤ μ (shellThin S (D * ν ^ n)) := hle
      _ ≤ ENNReal.ofReal (C * (D * ν ^ n)) := hthin _ hDν
      _ = ENNReal.ofReal (C * D * Real.exp (-(β * n))) := by
          rw [hexp n]; ring_nf
  -- Borel–Cantelli: the limsup of the pullbacks is null
  have hzero := measure_iInter_iUnion_exp_eq_zero μ
    (fun n : ℕ => ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
      shellThin S (D * ν ^ n)) (by positivity) hβpos hbound
  rw [ae_iff]
  have hset : {x : Work.EKLContract.X3 |
        ¬ (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) x ∉
            shellThin S (D * ν ^ n))}
      = ⋂ N : ℕ, ⋃ n ≥ N,
          ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) ⁻¹'
            shellThin S (D * ν ^ n) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · intro hx N
      push Not at hx
      obtain ⟨n, hn, hx⟩ := hx N
      exact ⟨n, hn, hx⟩
    · intro hx
      push Not
      intro N
      obtain ⟨n, hn, hx⟩ := hx N
      exact ⟨n, hn, hx⟩
  rw [hset]
  exact hzero

end Work.EKLC6Core
