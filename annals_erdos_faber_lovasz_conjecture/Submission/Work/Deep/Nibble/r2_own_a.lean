import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Reed.Prob.hoeffding_bounded_differences

set_option autoImplicit false
set_option linter.unusedVariables false
open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

/-- Changing a single coordinate changes the number of kept edges by at most one. -/
lemma keptF_card_update_le {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V))
    (f : 𝓖 → Bool) (e : 𝓖) (x : Bool) :
    |(((keptF 𝓖 (Function.update f e x)).card : ℝ)) - ((keptF 𝓖 f).card : ℝ)| ≤ 1 := by
  classical
  have hsub : ∀ ω ω' : 𝓖 → Bool, (∀ j, j ≠ e → ω' j = ω j) →
      keptF 𝓖 ω' ⊆ insert e (keptF 𝓖 ω) := by
    intro ω ω' h j hj
    rw [mem_keptF] at hj
    by_cases hje : j = e
    · exact Finset.mem_insert.mpr (Or.inl hje)
    · refine Finset.mem_insert.mpr (Or.inr ?_)
      rw [mem_keptF, ← h j hje]
      exact hj
  have h1 := hsub f (Function.update f e x) (fun j hj => Function.update_of_ne hj x f)
  have h2 := hsub (Function.update f e x) f (fun j hj => (Function.update_of_ne hj x f).symm)
  have h1' : ((keptF 𝓖 (Function.update f e x)).card : ℝ) ≤ (keptF 𝓖 f).card + 1 := by
    have := Finset.card_le_card h1
    have h3 : (insert e (keptF 𝓖 f)).card ≤ (keptF 𝓖 f).card + 1 := Finset.card_insert_le _ _
    have : (keptF 𝓖 (Function.update f e x)).card ≤ (keptF 𝓖 f).card + 1 := le_trans this h3
    exact_mod_cast this
  have h2' : ((keptF 𝓖 f).card : ℝ) ≤ (keptF 𝓖 (Function.update f e x)).card + 1 := by
    have h4 : (insert e (keptF 𝓖 (Function.update f e x))).card
        ≤ (keptF 𝓖 (Function.update f e x)).card + 1 := Finset.card_insert_le _ _
    have : (keptF 𝓖 f).card ≤ (keptF 𝓖 (Function.update f e x)).card + 1 :=
      le_trans (Finset.card_le_card h2) h4
    exact_mod_cast this
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem r2_X_tail {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {θ : ℝ}
    {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1) (hG : 𝓖.Nonempty) {t : ℝ}
    (ht : 50 * Real.sqrt (Nat.card 𝓖 : ℝ) < t) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ |((keptF 𝓖 ω).card : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ))|}
      ≤ 4 * Real.exp (-t ^ 2 / (16 * (Nat.card 𝓖 : ℝ))) := by
  classical
  have htpos : 0 < t := by
    have h1 : 0 < Real.sqrt (Nat.card 𝓖 : ℝ) := by
      rw [Real.sqrt_pos]
      obtain ⟨x, hx⟩ := hG
      haveI : Nonempty 𝓖 := ⟨⟨x, hx⟩⟩
      exact_mod_cast Nat.card_pos
    nlinarith
  have htail := Work.Deep.Reed.Prob.hoeffding_bounded_differences
    (μ := fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)
    (X := fun ω => ((keptF 𝓖 ω).card : ℝ)) (c := fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun i f x => keptF_card_update_le 𝓖 f i x) (t := t / 2) (by linarith)
  have hsum : (∑ i : 𝓖, (1 : ℝ) ^ 2) = (Nat.card 𝓖 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    norm_num
  rw [hsum] at htail
  have hsub : {ω : 𝓖 → Bool | t ≤ |((keptF 𝓖 ω).card : ℝ)
        - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ))|}
      ⊆ {ω : 𝓖 → Bool | t / 2 < |((keptF 𝓖 ω).card : ℝ)
        - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
            (fun ω => ((keptF 𝓖 ω).card : ℝ))|} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω ⊢
    have h1 : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ))
        = (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
            (fun ω => ((keptF 𝓖 ω).card : ℝ)) := rfl
    rw [h1] at hω
    linarith
  have hle : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t / 2 < |((keptF 𝓖 ω).card : ℝ)
          - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
              (fun ω => ((keptF 𝓖 ω).card : ℝ))|}
      = (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).prob
        {ω : 𝓖 → Bool | t / 2 < |((keptF 𝓖 ω).card : ℝ)
          - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
              (fun ω => ((keptF 𝓖 ω).card : ℝ))|} := rfl
  calc (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t ≤ |((keptF 𝓖 ω).card : ℝ)
          - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ((keptF 𝓖 ω).card : ℝ))|}
      ≤ (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).prob
        {ω : 𝓖 → Bool | t / 2 < |((keptF 𝓖 ω).card : ℝ)
          - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
              (fun ω => ((keptF 𝓖 ω).card : ℝ))|} := FinProb.prob_mono _ hsub
    _ = (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).prob
        {ω : 𝓖 → Bool | t / 2 < |((keptF 𝓖 ω).card : ℝ)
          - (FinProb.pi (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1)).exp
              (fun ω => ((keptF 𝓖 ω).card : ℝ))|} := hle
    _ ≤ 2 * Real.exp (-(2 * (t / 2) ^ 2) / (Nat.card 𝓖 : ℝ)) := htail
    _ = 2 * Real.exp (-(t ^ 2) / (2 * (Nat.card 𝓖 : ℝ))) := by ring_nf
    _ ≤ 4 * Real.exp (-t ^ 2 / (16 * (Nat.card 𝓖 : ℝ))) := by
        have hN : (0:ℝ) < (Nat.card 𝓖 : ℝ) := by
          obtain ⟨x, hx⟩ := hG
          haveI : Nonempty 𝓖 := ⟨⟨x, hx⟩⟩
          exact_mod_cast Nat.card_pos
        have h2 : Real.exp (-(t ^ 2) / (2 * (Nat.card 𝓖 : ℝ)))
            ≤ Real.exp (-t ^ 2 / (16 * (Nat.card 𝓖 : ℝ))) := by
          apply Real.exp_le_exp.mpr
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg t, hN]
        linarith [Real.exp_pos (-t ^ 2 / (16 * (Nat.card 𝓖 : ℝ))), h2]

end Work.Deep.Nibble
