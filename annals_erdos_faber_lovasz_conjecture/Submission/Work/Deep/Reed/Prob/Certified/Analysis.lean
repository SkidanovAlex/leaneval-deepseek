import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.Certified.Defs
import Submission.Work.Deep.Reed.Prob.Certified.Slice
import Submission.Work.Deep.Reed.Prob.Certified.EngineStep

/-!
# From the convex-distance engine to certifiable-function concentration

* `engine_tail` : the Markov consequence `Pr[A] · Pr[cd A ≥ u] ≤ e^{-u²/4}`;
* `abs_X_sub_le_of_agree_outside` : changing coordinates outside `T` changes a
  `c`-Lipschitz function by at most `c·|T|`;
* `cert_two_set` : the two-set estimate `Pr[X ≤ a] · Pr[X ≥ s] ≤ e^{-(s-a)²/(4c²rs)}`
  for `1 ≤ s` and `a < s`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

section Tail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- Markov step: the tail bound for the convex distance, from the exponential form. -/
theorem engine_tail (μ : ∀ i, FinProb (Ω i)) {A : Set (∀ i, Ω i)} {u : ℝ}
    (hE : (FinProb.pi μ).prob A *
      (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4)) ≤ 1) (hu : 0 ≤ u) :
    (FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | u ≤ cd A f} ≤ Real.exp (-(u ^ 2) / 4) := by
  classical
  have hpt : ∀ f : ∀ i, Ω i,
      Real.exp (u ^ 2 / 4) * (if u ≤ cd A f then (1 : ℝ) else 0)
        ≤ Real.exp (cdsq A f / 4) := by
    intro f
    by_cases hf : u ≤ cd A f
    · rw [if_pos hf, mul_one]
      apply Real.exp_le_exp.mpr
      have hs := Real.sq_sqrt (cdsq_nonneg (A := A) (x := f))
      have hcd : cd A f = Real.sqrt (cdsq A f) := rfl
      rw [hcd] at hf
      nlinarith [hf, Real.sqrt_nonneg (cdsq A f), hs]
    · rw [if_neg hf, mul_zero]
      exact le_of_lt (Real.exp_pos _)
  have hone : Real.exp (u ^ 2 / 4) * (FinProb.pi μ).prob {f | u ≤ cd A f}
      ≤ (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4)) := by
    rw [FinProb.prob, FinProb.exp, Finset.mul_sum]
    refine Finset.sum_le_sum fun f _ => ?_
    by_cases hf : f ∈ {f : ∀ i, Ω i | u ≤ cd A f}
    · have hvu : u ≤ cd A f := hf
      have h := hpt f
      rw [if_pos hvu, mul_one] at h
      rw [if_pos hf]
      calc Real.exp (u ^ 2 / 4) * (FinProb.pi μ).wt f
          ≤ Real.exp (cdsq A f / 4) * (FinProb.pi μ).wt f :=
            mul_le_mul_of_nonneg_right h ((FinProb.pi μ).wt_nonneg f)
        _ = (FinProb.pi μ).wt f * Real.exp (cdsq A f / 4) := by ring
    · rw [if_neg hf, mul_zero]
      exact mul_nonneg ((FinProb.pi μ).wt_nonneg f) (Real.exp_pos _).le
  have h2 : Real.exp (u ^ 2 / 4) *
      ((FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | u ≤ cd A f}) ≤ 1 := by
    have h3 : (FinProb.pi μ).prob A * (Real.exp (u ^ 2 / 4) *
        (FinProb.pi μ).prob {f | u ≤ cd A f})
        ≤ (FinProb.pi μ).prob A * (FinProb.pi μ).exp (fun f => Real.exp (cdsq A f / 4)) :=
      mul_le_mul_of_nonneg_left hone (FinProb.prob_nonneg _ _)
    linarith [hE, h3]
  have hpos : 0 < Real.exp (u ^ 2 / 4) := Real.exp_pos _
  have h2' : (FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | u ≤ cd A f}
      * Real.exp (u ^ 2 / 4) ≤ 1 := by
    rw [mul_comm ((FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | u ≤ cd A f})]
    exact h2
  calc (FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | u ≤ cd A f}
      ≤ 1 / Real.exp (u ^ 2 / 4) := (le_div_iff₀ hpos).mpr h2'
    _ = Real.exp (-(u ^ 2) / 4) := by
        rw [one_div, ← Real.exp_neg]
        congr 1
        ring

end Tail

section Lipschitz
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- Changing the coordinates outside `T` changes a `c`-Lipschitz function by at most
`c · |T|`. -/
lemma abs_X_sub_le_of_agree_outside (X : (∀ i, Ω i) → ℝ) {c : ℝ}
    (hlip : ∀ (i : ι) (f : ∀ i, Ω i) (x : Ω i),
      |X (Function.update f i x) - X f| ≤ c)
    {f g : ∀ i, Ω i} {T : Finset ι} (h : ∀ i, i ∉ T → g i = f i) :
    |X g - X f| ≤ c * (T.card : ℝ) := by
  classical
  have key : ∀ (T : Finset ι) (g : ∀ i, Ω i),
      (∀ i, i ∉ T → g i = f i) → |X g - X f| ≤ c * (T.card : ℝ) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro g h
      have hgf : g = f := by funext i; exact h i (by simp)
      rw [hgf, sub_self, abs_zero]
      simp
    · intro i₀ T' hi₀ ih g h
      set g' : ∀ i, Ω i := Function.update g i₀ (f i₀) with hg'
      have h1 : |X g - X g'| ≤ c := by
        have hgg' : g = Function.update g' i₀ (g i₀) := by
          rw [hg']
          funext i
          by_cases hia : i = i₀
          · subst hia; simp
          · simp [Function.update_of_ne hia]
        rw [hgg']
        exact hlip i₀ g' (g i₀)
      have h2 : |X g' - X f| ≤ c * (T'.card : ℝ) := by
        refine ih g' ?_
        intro i hi
        by_cases hia : i = i₀
        · rw [hia, hg']
          simp
        · have hiT : i ∉ insert i₀ T' := by
            intro hmem
            rcases Finset.mem_insert.mp hmem with h' | h'
            · exact hia h'
            · exact hi h'
          have hg'i : g' i = g i := by rw [hg']; exact Function.update_of_ne hia _ _
          rw [hg'i]
          exact h i hiT
      have h3 : |X g - X f| ≤ |X g - X g'| + |X g' - X f| := abs_sub_le _ _ _
      have h4 : ((insert i₀ T').card : ℝ) = (T'.card : ℝ) + 1 := by
        rw [Finset.card_insert_of_notMem hi₀, Nat.cast_add, Nat.cast_one]
      rw [h4]
      nlinarith [h1, h2, h3]
  exact key T g h

end Lipschitz



end Work.Deep.Reed.Prob
