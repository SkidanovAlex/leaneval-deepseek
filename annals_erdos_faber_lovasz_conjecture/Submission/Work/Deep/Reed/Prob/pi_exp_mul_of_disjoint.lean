import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.Expectation
import Submission.Work.Deep.Reed.Prob.FunDepends
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint

/-!
# Expectations factorise over disjoint coordinate sets

In a product of finite probability spaces, two real-valued random variables which depend only on
disjoint sets of coordinates are uncorrelated: `E[XY] = E[X]·E[Y]`.

The proof writes each of `X`, `Y` as a finite linear combination of indicators of its level sets
(which inherit the dependence on the corresponding coordinate set) and applies the event-level
independence lemma `Prob.pi_prob_inter_eq_mul_of_disjoint` termwise.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-- The expectation of an indicator is the probability of the event. -/
private lemma exp_indicator {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) (P : Ω → Prop)
    [DecidablePred P] :
    μ.exp (fun ω => if P ω then (1 : ℝ) else 0) = μ.prob {ω | P ω} := by
  rw [FinProb.exp, FinProb.prob]
  exact Finset.sum_congr rfl fun ω _ => by by_cases h : P ω <;> simp [h]

/-- Expectation of a finite sum of real random variables. -/
private lemma exp_sum_finset {Ω : Type*} [Fintype Ω] (μ : FinProb Ω) {ι : Type*}
    (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.exp (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.exp (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FinProb.exp_const]
  | insert a s ha ih =>
      have hpt : (fun ω => ∑ i ∈ insert a s, X i ω) = (fun ω => X a ω + ∑ i ∈ s, X i ω) :=
        funext fun ω => Finset.sum_insert ha
      rw [hpt, FinProb.exp_add, ih, Finset.sum_insert ha]

/-- In a product of finite probability spaces, the expectation of a product of two real-valued
random variables which depend only on disjoint sets of coordinates factorises. -/
theorem pi_exp_mul_of_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i))
    {S T : Finset ι} (hST : Disjoint S T) {X Y : (∀ i, Ω i) → ℝ}
    (hX : FunDepends S X) (hY : FunDepends T Y) :
    (FinProb.pi μ).exp (fun f => X f * Y f)
      = (FinProb.pi μ).exp X * (FinProb.pi μ).exp Y := by
  classical
  set sX : Finset ℝ := Finset.image X Finset.univ with hsX
  set sY : Finset ℝ := Finset.image Y Finset.univ with hsY
  have memX : ∀ f : ∀ i, Ω i, X f ∈ sX := fun f =>
    Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩
  have memY : ∀ f : ∀ i, Ω i, Y f ∈ sY := fun f =>
    Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩
  have decX : ∀ f : ∀ i, Ω i, X f = ∑ a ∈ sX, a * (if X f = a then (1 : ℝ) else 0) := by
    intro f
    rw [Finset.sum_eq_single (X f)]
    · simp
    · intro a _ ha
      rw [if_neg (Ne.symm ha), mul_zero]
    · intro h
      exact absurd (memX f) h
  have decY : ∀ f : ∀ i, Ω i, Y f = ∑ b ∈ sY, b * (if Y f = b then (1 : ℝ) else 0) := by
    intro f
    rw [Finset.sum_eq_single (Y f)]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (memY f) h
  -- level sets inherit the dependence hypotheses
  have depX : ∀ a : ℝ, DependsOn S {f : ∀ i, Ω i | X f = a} := fun a f f' h => by
    simp only [Set.mem_setOf_eq]
    rw [hX f f' h]
  have depY : ∀ b : ℝ, DependsOn T {f : ∀ i, Ω i | Y f = b} := fun b f f' h => by
    simp only [Set.mem_setOf_eq]
    rw [hY f f' h]
  have hprob : ∀ a b : ℝ,
      (FinProb.pi μ).prob {f : ∀ i, Ω i | X f = a ∧ Y f = b}
        = (FinProb.pi μ).prob {f : ∀ i, Ω i | X f = a}
          * (FinProb.pi μ).prob {f : ∀ i, Ω i | Y f = b} := by
    intro a b
    rw [show {f : ∀ i, Ω i | X f = a ∧ Y f = b}
          = {f : ∀ i, Ω i | X f = a} ∩ {f : ∀ i, Ω i | Y f = b} from by
        ext f; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]]
    exact pi_prob_inter_eq_mul_of_disjoint μ hST (depX a) (depY b)
  -- the pointwise expansion of the product
  have hpt : ∀ f : ∀ i, Ω i, X f * Y f
      = ∑ a ∈ sX, ∑ b ∈ sY, (a * b) * (if (X f = a ∧ Y f = b) then (1 : ℝ) else 0) := by
    intro f
    conv_lhs => rw [decX f, decY f]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases h1 : X f = a <;> by_cases h2 : Y f = b <;> simp [h1, h2]
  have hexp : (FinProb.pi μ).exp (fun f => X f * Y f)
      = ∑ a ∈ sX, ∑ b ∈ sY, (a * b) * ((FinProb.pi μ).prob {f : ∀ i, Ω i | X f = a}
          * (FinProb.pi μ).prob {f : ∀ i, Ω i | Y f = b}) := by
    rw [show (fun f : ∀ i, Ω i => X f * Y f)
        = (fun f => ∑ a ∈ sX, ∑ b ∈ sY,
            (a * b) * (if (X f = a ∧ Y f = b) then (1 : ℝ) else 0)) from funext hpt]
    rw [exp_sum_finset]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [exp_sum_finset]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [FinProb.exp_mul_left, exp_indicator, hprob a b]
  have hexpX : (FinProb.pi μ).exp X
      = ∑ a ∈ sX, a * (FinProb.pi μ).prob {f : ∀ i, Ω i | X f = a} := by
    have h : (∑ a ∈ sX, a * (FinProb.pi μ).prob {f : ∀ i, Ω i | X f = a})
        = (FinProb.pi μ).exp (fun f : ∀ i, Ω i =>
            ∑ a ∈ sX, a * (if X f = a then (1 : ℝ) else 0)) := by
      rw [exp_sum_finset]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [FinProb.exp_mul_left, exp_indicator]
    rw [h, show (fun f : ∀ i, Ω i => ∑ a ∈ sX,
        a * (if X f = a then (1 : ℝ) else 0)) = X from (funext decX).symm]
  have hexpY : (FinProb.pi μ).exp Y
      = ∑ b ∈ sY, b * (FinProb.pi μ).prob {f : ∀ i, Ω i | Y f = b} := by
    have h : (∑ b ∈ sY, b * (FinProb.pi μ).prob {f : ∀ i, Ω i | Y f = b})
        = (FinProb.pi μ).exp (fun f : ∀ i, Ω i =>
            ∑ b ∈ sY, b * (if Y f = b then (1 : ℝ) else 0)) := by
      rw [exp_sum_finset]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [FinProb.exp_mul_left, exp_indicator]
    rw [h, show (fun f : ∀ i, Ω i => ∑ b ∈ sY,
        b * (if Y f = b then (1 : ℝ) else 0)) = Y from (funext decY).symm]
  rw [hexp, hexpX, hexpY, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Work.Deep.Reed.Prob
