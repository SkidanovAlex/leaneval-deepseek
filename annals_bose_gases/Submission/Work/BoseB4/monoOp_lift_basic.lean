import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.Q3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.monoOp_lift_basic` — elementary algebra of `monoOp`, `lift`, `a₀`, `a₀†`

The anti-normal monomial `monoOp p q B = a₀^p (a₀†)^q (lift B)` (`Defs.lean`) has,
for the small exponent pairs occurring in FS's row `Q̃₃` (`eq:3Qtilde`,
`Q3Defs.lean`), the elementary forms

* `monoOp 0 1 B = a₀† (lift B)` and `monoOp 1 0 B = a₀ (lift B)` (`monoOp_zero_one`,
  `monoOp_one_zero`);
* `monoOp 1 1 B − monoOp 0 0 B = (a₀† a₀) (lift B)` (`monoOp_one_one_sub_zero_zero`),
  the `a₀ a₀† = a₀† a₀ + 1` identity in the exact shape in which the `s = k` terms
  of `Q̃₃` need it.

It is additive and `ℂ`-linear in `B` (`MonoOp.lean`), hence distributes over finite
sums (`monoOp_sum`) and over the `if … then … else 0` summands by which the rows
separate the `s = k` from the `s ≠ k` terms (`monoOp_ite_left`, `monoOp_ite_right`).

The last four lemmas are the `lift`/`a₀` bookkeeping identities needed to put a
word with `a₀` in the middle into anti-normal form: `lift` commutes with `a₀` and
`a₀†` (`Defs.lift_comm_a0`, `Defs.lift_comm_a0d`) and combines with itself
(`Defs.lift_comp`).
-/

noncomputable section

open scoped lp BigOperators

namespace Work.BoseB4

set_option autoImplicit false

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## The small anti-normal monomials -/

@[simp]
lemma monoOp_zero_one (B : E →ₗ[ℂ] E) : monoOp 0 1 B = a0d.comp (lift B) := by
  simp only [monoOp, a0pow_zero, a0dpow_zero, a0dpow_succ]
  ext x; simp

@[simp]
lemma monoOp_one_zero (B : E →ₗ[ℂ] E) : monoOp 1 0 B = a0.comp (lift B) := by
  simp only [monoOp, a0pow_zero, a0dpow_zero, a0pow_succ]
  ext x; simp

/-- `a₀ a₀† − 1 = a₀† a₀` in the anti-normal slot: `monoOp 1 1 B − monoOp 0 0 B` is the
normally ordered `n₀ ⊗ B`. -/
lemma monoOp_one_one_sub_zero_zero (B : E →ₗ[ℂ] E) :
    monoOp 1 1 B - monoOp 0 0 B = (a0d.comp a0).comp (lift B) := by
  have h1 : ∀ f : FockCore E →ₗ[ℂ] FockCore E, (1 : FockCore E →ₗ[ℂ] FockCore E).comp f = f :=
    fun f => by ext x; simp
  simp only [monoOp, a0pow_zero, a0dpow_zero, a0pow_succ, a0dpow_succ, h1]
  rw [← LinearMap.comp_assoc, ccr, LinearMap.add_comp, h1]
  abel

/-! ## Additivity over finite sums and `if` -/

lemma monoOp_sum {ι : Type*} [DecidableEq ι] (p q : ℕ) (s : Finset ι)
    (f : ι → E →ₗ[ℂ] E) :
    monoOp p q (∑ i ∈ s, f i) = ∑ i ∈ s, monoOp p q (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ht ih
    rw [Finset.sum_insert ht, Finset.sum_insert ht, monoOp_add, ih]

lemma monoOp_ite_left (p q : ℕ) {c : Prop} [Decidable c] (A : E →ₗ[ℂ] E) :
    monoOp p q (if c then A else 0) = if c then monoOp p q A else 0 := by
  by_cases h : c <;> simp [h]

lemma monoOp_ite_right (p q : ℕ) {c : Prop} [Decidable c] (A : E →ₗ[ℂ] E) :
    monoOp p q (if c then 0 else A) = if c then 0 else monoOp p q A := by
  by_cases h : c <;> simp [h]

/-! ## Pushing `a₀`, `a₀†` through a lift -/

/-- `lift B · a₀ · lift C = a₀ · lift (B ∘ C)`. -/
lemma lift_comp_a0_comp (B C : E →ₗ[ℂ] E) :
    (lift B).comp (a0.comp (lift C)) = a0.comp (lift (B.comp C)) := by
  rw [← LinearMap.comp_assoc (lift C) a0 (lift B), lift_comm_a0 B,
      LinearMap.comp_assoc (lift C) (lift B) a0, ← lift_comp B C]

/-- `lift B · a₀† · lift C = a₀† · lift (B ∘ C)`. -/
lemma lift_comp_a0d_comp (B C : E →ₗ[ℂ] E) :
    (lift B).comp (a0d.comp (lift C)) = a0d.comp (lift (B.comp C)) := by
  rw [← LinearMap.comp_assoc (lift C) a0d (lift B), lift_comm_a0d B,
      LinearMap.comp_assoc (lift C) (lift B) a0d, ← lift_comp B C]

/-- `lift B · lift C · lift A · a₀ = a₀ · lift (B ∘ C ∘ A)`. -/
lemma lift_comp_lift_comp_a0 (B C A : E →ₗ[ℂ] E) :
    (lift B).comp ((lift C).comp ((lift A).comp a0)) = a0.comp (lift (B.comp (C.comp A))) := by
  rw [lift_comm_a0 A, lift_comp_a0_comp C A, lift_comp_a0_comp B (C.comp A)]

/-- `lift B · a₀† · lift A · a₀ = (a₀† a₀) · lift (B ∘ A)`. -/
lemma lift_comp_a0d_comp_a0 (B A : E →ₗ[ℂ] E) :
    (lift B).comp (a0d.comp ((lift A).comp a0)) = (a0d.comp a0).comp (lift (B.comp A)) := by
  rw [← LinearMap.comp_assoc a0 (lift A) a0d,
      ← LinearMap.comp_assoc a0 (a0d.comp (lift A)) (lift B),
      lift_comp_a0d_comp B A, LinearMap.comp_assoc a0 (lift (B.comp A)) a0d,
      lift_comm_a0 (B.comp A), ← LinearMap.comp_assoc (lift (B.comp A)) a0 a0d]

end Generic

end Work.BoseB4
