import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.hoeffding_bounded_differences

/-!
# Fubini for a sum of one-coordinate functions on a product of uniforms

The engine of the computation is the *marginal* formula for a product measure:
in a product of finite probability spaces, the expectation of a function of a
single coordinate is the expectation under that coordinate's marginal.  It is
obtained from the disintegration identity `FinProb.freeze_exp` together with the
elementary observation that, once a coordinate is frozen at a point mass, a
function of that coordinate is constant on the support.

Summing the marginal formula over the coordinates (linearity of expectation)
gives `pi_uniform_exp_sum`, the statement requested here: on the product of the
uniform measures on `Fin (c i)`, the expectation of `j ↦ ∑ i, Y i (j i)` is the
sum of the averages `(∑ x, Y i x) / c i`.
-/

open scoped BigOperators

namespace Work.Deep.Nibble

/-- Expectation under a *frozen* product measure only sees the values of the
random variable on the fibre `{f | f j = x}`.  (The `exp` analogue of
`FinProb.freeze_prob_congr`.) -/
lemma pi_uniform_exp_freeze_congr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (j : ι)
    (x : Ω j) {Z Z' : (∀ i, Ω i) → ℝ} (h : ∀ f, f j = x → Z f = Z' f) :
    (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp Z
      = (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp Z' := by
  rw [Work.Deep.Reed.FinProb.exp, Work.Deep.Reed.FinProb.exp]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hfx : f j = x
  · rw [h f hfx]
  · have hw : (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).wt f = 0 := by
      rw [Work.Deep.Reed.FinProb.pi_freeze_wt,
        Work.Deep.Reed.FinProb.point_wt_of_ne hfx, mul_zero]
    rw [hw, zero_mul, zero_mul]

/-- **The marginal formula**: in a product of finite probability spaces, the
expectation of a function of the single coordinate `j` is computed by the `j`-th
marginal. -/
lemma pi_uniform_exp_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, Work.Deep.Reed.FinProb (Ω i))
    (j : ι) (g : Ω j → ℝ) :
    (Work.Deep.Reed.FinProb.pi μ).exp (fun f => g (f j)) = (μ j).exp g := by
  rw [Work.Deep.Reed.Prob.freeze_exp μ j (fun f => g (f j))]
  have hterm : ∀ x : Ω j,
      (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp (fun f => g (f j))
        = g x := by
    intro x
    rw [pi_uniform_exp_freeze_congr μ j x (Z' := fun _ => g x) (fun f hf => by rw [hf]),
      Work.Deep.Reed.FinProb.exp_const]
  calc ∑ x : Ω j, (μ j).wt x *
        (Work.Deep.Reed.FinProb.pi (Work.Deep.Reed.FinProb.freeze μ j x)).exp
          (fun f => g (f j))
      = ∑ x : Ω j, (μ j).wt x * g x := Finset.sum_congr rfl fun x _ => by rw [hterm x]
    _ = (μ j).exp g := rfl

/-- **Fubini for a sum of one-coordinate functions** in an arbitrary product
measure: the expectation of `f ↦ ∑ i, Y i (f i)` is the sum of the marginal
expectations. -/
lemma pi_uniform_exp_sum_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, Work.Deep.Reed.FinProb (Ω i))
    (Y : ∀ i, Ω i → ℝ) :
    (Work.Deep.Reed.FinProb.pi μ).exp (fun f => ∑ i, Y i (f i))
      = ∑ i, (μ i).exp (Y i) := by
  rw [Work.Deep.Reed.FinProb.exp_sum (Work.Deep.Reed.FinProb.pi μ) (fun i f => Y i (f i))]
  exact Finset.sum_congr rfl fun i _ => pi_uniform_exp_apply μ i (Y i)

/-- Expectation under the uniform measure on `Fin c`. -/
lemma pi_uniform_exp_uniform_eq (c : ℕ) [NeZero c] (Y : Fin c → ℝ) :
    (Work.Deep.Reed.FinProb.uniform (Fin c)).exp Y = (∑ x : Fin c, Y x) / (c : ℝ) := by
  rw [Work.Deep.Reed.FinProb.exp]
  have hwt : ∀ x : Fin c, (Work.Deep.Reed.FinProb.uniform (Fin c)).wt x = ((c : ℝ))⁻¹ := by
    intro x
    show (Fintype.card (Fin c) : ℝ)⁻¹ = ((c : ℝ))⁻¹
    rw [Fintype.card_fin]
  rw [Finset.sum_congr rfl (fun x _ => by rw [hwt x]), ← Finset.mul_sum, div_eq_inv_mul]

/-- **Fubini for a sum of one-coordinate functions on a product of uniforms.**  On the product of the uniform measures on `Fin (c i)`, the expectation of `j ↦ ∑ i, Y i (j i)` is the sum of the averages `(∑ x, Y i x)/c i`.  The weights of the product measure are the constant `∏ i, (c i)⁻¹`, so the computation is finite double counting. -/
theorem pi_uniform_exp_sum {p : ℕ} (c : Fin p → ℕ) [∀ i, NeZero (c i)]
    (Y : ∀ i, Fin (c i) → ℝ) :
    (Work.Deep.Reed.FinProb.pi (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i)))).exp
        (fun j => ∑ i, Y i (j i))
      = ∑ i, (∑ x : Fin (c i), Y i x) / (c i : ℝ) := by
  rw [pi_uniform_exp_sum_apply (fun i => Work.Deep.Reed.FinProb.uniform (Fin (c i))) Y]
  exact Finset.sum_congr rfl fun i _ => pi_uniform_exp_uniform_eq (c i) (Y i)

end Work.Deep.Nibble
