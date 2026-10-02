import Submission.Work.Deep.Nibble.r2_own_b

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem r2_exp_adv (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((collMult 𝓖 ω : ℕ) : ℝ))
      = ∑ v : V, ((hd 𝓖 v : ℝ) * p - (hd 𝓖 v : ℝ) * p * (1 - p) ^ (hd 𝓖 v - 1))
  ∧ (∀ v : V, (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ((Wv 𝓖 ω v : ℕ) : ℝ))
      = ∑ e ∈ thruF 𝓖 v, (1 - p) ^ (Bset 𝓖 v e).card) := by
  classical
  have hbasic := r2_exp_basic 𝓖 hp0 hp1
  constructor
  · have hpt : ∀ ω : 𝓖 → Bool, ((collMult 𝓖 ω : ℕ) : ℝ)
        = ∑ v : V, (((if 2 ≤ kAtF 𝓖 ω v then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ) := by
      intro ω
      rw [collMult, Nat.cast_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [kAt_eq_kAtF]
    rw [show (fun ω : 𝓖 → Bool => ((collMult 𝓖 ω : ℕ) : ℝ))
        = (fun ω => ∑ v : V, (((if 2 ≤ kAtF 𝓖 ω v then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ)) from funext hpt]
    rw [FinProb.exp_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hg : ∀ ω : 𝓖 → Bool, ((((if 2 ≤ kAtF 𝓖 ω v then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ))
        = ((kAtF 𝓖 ω v : ℕ) : ℝ)
          - (((if kAtF 𝓖 ω v = 1 then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ) := by
      intro ω
      by_cases h : 2 ≤ kAtF 𝓖 ω v
      · have hk : kAtF 𝓖 ω v ≠ 1 := by omega
        rw [if_pos h, if_neg hk]
        simp
      · have hk : kAtF 𝓖 ω v = 0 ∨ kAtF 𝓖 ω v = 1 := by omega
        rcases hk with hk | hk <;> simp [hk]
    rw [show (fun ω : 𝓖 → Bool => (((if 2 ≤ kAtF 𝓖 ω v then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ))
        = (fun ω => ((kAtF 𝓖 ω v : ℕ) : ℝ)
            - (((if kAtF 𝓖 ω v = 1 then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ)) from funext hg]
    rw [FinProb.exp_sub, hbasic.2.2.1 v]
    have h2 : (edgeMeasure 𝓖 p hp0 hp1).exp
          (fun ω => (((if kAtF 𝓖 ω v = 1 then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ))
        = (hd 𝓖 v : ℝ) * p * (1 - p) ^ (hd 𝓖 v - 1) := by
      have hpt' : (fun ω : 𝓖 → Bool => (((if kAtF 𝓖 ω v = 1 then kAtF 𝓖 ω v else 0 : ℕ)) : ℝ))
          = (fun ω => if kAtF 𝓖 ω v = 1 then (1 : ℝ) else 0) := by
        funext ω
        by_cases h : kAtF 𝓖 ω v = 1 <;> simp [h]
      rw [hpt', FinProb.exp_indicator]
      exact hbasic.2.2.2.1 v
    rw [h2]
  · intro v
    have hpt : ∀ ω : 𝓖 → Bool, ((Wv 𝓖 ω v : ℕ) : ℝ)
        = ∑ e ∈ thruF 𝓖 v, (if ∀ f ∈ Bset 𝓖 v e, ω f = false then (1 : ℝ) else 0) := by
      intro ω
      rw [Wv, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h : ∀ f ∈ Bset 𝓖 v e, ω f = false <;> simp [h]
    rw [show (fun ω : 𝓖 → Bool => ((Wv 𝓖 ω v : ℕ) : ℝ))
        = (fun ω => ∑ e ∈ thruF 𝓖 v,
            (if ∀ f ∈ Bset 𝓖 v e, ω f = false then (1 : ℝ) else 0)) from funext hpt]
    rw [FinProb.exp_sum_finset]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [FinProb.exp_indicator, edgeMeasure_prob_unkept]

end Work.Deep.Nibble
