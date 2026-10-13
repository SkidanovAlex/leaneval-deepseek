import Mathlib
import Submission.Work.WilkiesH.Interp.iteratedDeriv_mul_bound_sharp

set_option linter.unusedVariables false

namespace Work.WilkiesH.Interp

/-- Strong form of `iteratedDeriv_prod_bound_sharp`, in which the hypothesis on the derivatives of
the factors is phrased *uniformly* for all orders `k ≤ j`, hence also at order `k = 0`, where the
bound reads `|g i s₀| ≤ c ^ 0 = 1` and so recovers the value bound.  This is the form that makes
the induction on the number of factors go through: the two-factor Leibniz rule produces derivatives
of the sub-product at every order below `j`. -/
theorem iteratedDeriv_prod_bound_sharp_aux (j : ℕ) {ι : Type*} :
    ∀ (s : Finset ι) (g : ι → ℝ → ℝ) (s₀ c : ℝ), 0 ≤ c →
      (∀ i ∈ s, ContDiffAt ℝ (j : ℕ) (g i) s₀) →
      (∀ i ∈ s, ∀ k, k ≤ j → |iteratedDeriv k (g i) s₀| ≤ c ^ k) →
      ∀ m, m ≤ j → |iteratedDeriv m (fun x => ∏ i ∈ s, g i x) s₀| ≤ ((s.card : ℝ) * c) ^ m := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g s₀ c hc hdiff hder m hm
    have hfun : (fun x => ∏ i ∈ (∅ : Finset ι), g i x) = fun _ => (1 : ℝ) := by
      funext x; simp
    rw [hfun, iteratedDeriv_const]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; norm_num
    · have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp h
      rw [ite_eq_right hm0, abs_zero]
      simp [Finset.card_empty, zero_pow hm0]
  | insert a t ha ih =>
    intro g s₀ c hc hdiff hder m hm
    -- Split off the last factor `G = g a` from the sub-product `P` over `t`.
    set P : ℝ → ℝ := fun x => ∏ i ∈ t, g i x with hP
    set G : ℝ → ℝ := g a with hG
    have hcard : ((insert a t).card : ℝ) = (t.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem ha]; push_cast; ring
    have hdiff_t : ∀ i ∈ t, ContDiffAt ℝ (j : ℕ) (g i) s₀ :=
      fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hder_t : ∀ i ∈ t, ∀ k, k ≤ j → |iteratedDeriv k (g i) s₀| ≤ c ^ k :=
      fun i hi k hk => hder i (Finset.mem_insert_of_mem hi) k hk
    -- Inductive hypothesis for the sub-product, valid at every order `k ≤ j`.
    have hIH : ∀ k, k ≤ j → |iteratedDeriv k P s₀| ≤ ((t.card : ℝ) * c) ^ k :=
      fun k hk => ih g s₀ c hc hdiff_t hder_t k hk
    have hPdiff : ContDiffAt ℝ (m : ℕ) P s₀ := by
      rw [hP]
      exact (contDiffAt_prod (fun i hi => hdiff i (Finset.mem_insert_of_mem hi))).of_le
        (by exact_mod_cast hm)
    have hGdiff : ContDiffAt ℝ (m : ℕ) G s₀ :=
      (hdiff a (Finset.mem_insert_self a t)).of_le (by exact_mod_cast hm)
    have huni : ∀ k, k ≤ j → |iteratedDeriv k G s₀| ≤ c ^ k :=
      fun k hk => hder a (Finset.mem_insert_self a t) k hk
    have hA : (0 : ℝ) ≤ (t.card : ℝ) * c := mul_nonneg (Nat.cast_nonneg _) hc
    -- Sharp Leibniz bound for the two factors `P` and `G`.
    have hmain : |iteratedDeriv m (P * G) s₀| ≤ (((t.card : ℝ) * c) + c) ^ m :=
      iteratedDeriv_mul_bound_sharp hm hA hc hPdiff hGdiff hIH huni
    have hfun : (fun x => ∏ i ∈ insert a t, g i x) = P * G := by
      funext x
      simp only [Finset.prod_insert ha, Pi.mul_apply, hP, hG]
      ring
    rw [hfun, hcard]
    have hbase : ((t.card : ℝ) + 1) * c = (t.card : ℝ) * c + c := by ring
    rw [hbase]
    exact hmain

/-- **Sharp bound for the iterated derivatives of a finite product.**

Let `g i` be `C^j` at `s₀`, with `|g i s₀| ≤ 1` and `|g i^{(k)}(s₀)| ≤ c ^ k` for `1 ≤ k ≤ j`, where
`c ≥ 0`.  Then for every `m ≤ j`, the `m`-th iterated derivative of `∏ i ∈ s, g i` at `s₀` is
bounded by `((card s) * c) ^ m`. -/
theorem iteratedDeriv_prod_bound_sharp {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ) (s₀ : ℝ)
    {c : ℝ} (hc : 0 ≤ c) {j : ℕ}
    (hdiff : ∀ i ∈ s, ContDiffAt ℝ (j : ℕ) (g i) s₀)
    (hval : ∀ i ∈ s, |g i s₀| ≤ 1)
    (hder : ∀ i ∈ s, ∀ k, 1 ≤ k → k ≤ j → |iteratedDeriv k (g i) s₀| ≤ c ^ k) :
    ∀ m, m ≤ j → |iteratedDeriv m (fun x => ∏ i ∈ s, g i x) s₀| ≤ ((s.card : ℝ) * c) ^ m := by
  refine iteratedDeriv_prod_bound_sharp_aux j s g s₀ c hc hdiff ?_
  -- At order `0` the uniform bound `|g i s₀| ≤ c ^ 0 = 1` is exactly the value hypothesis.
  intro i hi k hk
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    simpa using hval i hi
  · exact hder i hi k h hk

end Work.WilkiesH.Interp
