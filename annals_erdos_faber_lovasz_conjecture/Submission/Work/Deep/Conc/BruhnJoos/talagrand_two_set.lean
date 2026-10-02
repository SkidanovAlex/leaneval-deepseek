import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Basic
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Conc.BruhnJoos.reed_adapter
import Submission.Work.Deep.Reed.Prob.Certified.Analysis

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Conc.BruhnJoos

theorem talagrand_two_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)] (hne : ∀ i, Nonempty (π i))
    (A B : Set (∀ i, π i)) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : ∀ ω ∈ B, ∃ α : ι → ℝ, (∑ i, α i ^ 2) = 1 ∧ (∀ i, 0 ≤ α i) ∧
      ∀ ω' ∈ A, τ ≤ ∑ i, α i * (if ω i ≠ ω' i then (1 : ℝ) else 0)) :
    Work.Deep.Conc.prob A * Work.Deep.Conc.prob B ≤ Real.exp (- τ ^ 2 / 4) := by
  classical
  by_cases hAne : A.Nonempty
  · haveI : ∀ i, Nonempty (π i) := hne
    -- the uniform measure has full support
    have hfull : ∀ (i : ι) (x : π i), 0 < (Work.Deep.Reed.FinProb.uniform (π i)).wt x := by
      intro i x
      show 0 < ((Fintype.card (π i) : ℝ))⁻¹
      exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    -- Talagrand's convex-distance inequality at `A`
    have hEng : (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).prob A *
        (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).exp
          (fun f => Real.exp (Work.Deep.Reed.Prob.cdsq A f / 4)) ≤ 1 :=
      Work.Deep.Reed.Prob.engine_all ι π (fun i => Work.Deep.Reed.FinProb.uniform (π i)) hfull A
    have htail := Work.Deep.Reed.Prob.engine_tail (Ω := π)
      (fun i => Work.Deep.Reed.FinProb.uniform (π i)) (A := A) (u := τ) hEng hτ
    -- every `ω ∈ B` has convex distance at least `τ` from `A`
    have hBsub : B ⊆ {f : ∀ i, π i | τ ≤ Work.Deep.Reed.Prob.cd A f} := by
      intro ω hω
      obtain ⟨α, hαsq, hαnn, hα⟩ := h ω hω
      have hwit : τ ^ 2 ≤ Work.Deep.Reed.Prob.sqnorm α * Work.Deep.Reed.Prob.cdsq A ω :=
        Work.Deep.Reed.Prob.cdsq_ge_of_witness (A := A) (x := ω) (a := α) hαnn hAne (D := τ) hτ
          (fun y hy => by
            refine le_trans (hα y hy) (Finset.sum_le_sum fun i _ => ?_)
            by_cases hne : ω i = y i
            · rw [if_neg (by intro hh; exact hh hne), Work.Deep.Reed.Prob.disag_eq_zero.mpr hne]
            · rw [if_pos hne, Work.Deep.Reed.Prob.disag_eq_one.mpr hne])
      have hsq : Work.Deep.Reed.Prob.sqnorm α = 1 := by
        rw [Work.Deep.Reed.Prob.sqnorm]; exact hαsq
      have hcdsq : τ ^ 2 ≤ Work.Deep.Reed.Prob.cdsq A ω := by
        rw [hsq, one_mul] at hwit; exact hwit
      show τ ≤ Work.Deep.Reed.Prob.cd A ω
      show τ ≤ Real.sqrt (Work.Deep.Reed.Prob.cdsq A ω)
      rw [← Real.sqrt_sq hτ]
      exact Real.sqrt_le_sqrt hcdsq
    have hmono : Work.Deep.Conc.prob B
        ≤ Work.Deep.Conc.prob {f : ∀ i, π i | τ ≤ Work.Deep.Reed.Prob.cd A f} :=
      Work.Deep.Conc.prob_mono hBsub
    -- identify the measure with the uniform measure of this development
    have hAconv : (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).prob A
        = Work.Deep.Conc.prob A := pi_uniform_prob_eq hne A
    have hSconv : (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (π i))).prob
        {f : ∀ i, π i | τ ≤ Work.Deep.Reed.Prob.cd A f}
        = Work.Deep.Conc.prob {f : ∀ i, π i | τ ≤ Work.Deep.Reed.Prob.cd A f} :=
      pi_uniform_prob_eq hne _
    rw [hAconv, hSconv] at htail
    calc Work.Deep.Conc.prob A * Work.Deep.Conc.prob B
        ≤ Work.Deep.Conc.prob A *
            Work.Deep.Conc.prob {f : ∀ i, π i | τ ≤ Work.Deep.Reed.Prob.cd A f} :=
          mul_le_mul_of_nonneg_left hmono (Work.Deep.Conc.prob_nonneg A)
      _ ≤ Real.exp (-(τ ^ 2) / 4) := htail
  · have hAe : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hAne
    rw [hAe, Work.Deep.Conc.prob_empty, zero_mul]
    exact (Real.exp_pos _).le

end Work.Deep.Conc.BruhnJoos
