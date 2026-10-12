import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Submission.Work.SmallBoxA0.OneDPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.SmallBoxA0

/-- Tail flux as an interval integral: `TailI p R r = ∫_r^R s * p s ds`. -/
def TailI (p : ℝ → ℝ) (R r : ℝ) : ℝ := ∫ s in r..R, s * p s

/-- Shell potential in interval-integral form: `ShellI p R r = ∫_0^r TailI p R t dt`. -/
def ShellI (p : ℝ → ℝ) (R r : ℝ) : ℝ := ∫ t in (0 : ℝ)..r, TailI p R t

@[simp] lemma TailI_self (p : ℝ → ℝ) (R : ℝ) : TailI p R R = 0 := by
  simp [TailI]

@[simp] lemma ShellI_self (p : ℝ → ℝ) (R : ℝ) : ShellI p R 0 = 0 := by
  simp [ShellI]

/-- `∫` over `Set.Ioo a b` equals the interval integral `∫_a^b` when `a ≤ b`. -/
lemma integral_Ioo_eq_intervalIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → E) :
    ∫ x in Set.Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- `AbsolutelyContinuousOnInterval` only depends on the values of the function on `uIcc a b`. -/
lemma absolutelyContinuousOnInterval_congr {f g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Set.uIcc a b, f x = g x) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hf ε hε
  exact ⟨δ, hδ, fun E hE hlen => lt_of_le_of_lt (Finset.sum_le_sum (fun i hi => by
    have h1 := (hE.1 i hi).1
    have h2 := (hE.1 i hi).2
    rw [← h _ h1, ← h _ h2])) (H E hE hlen)⟩

end Work.SmallBoxA0
