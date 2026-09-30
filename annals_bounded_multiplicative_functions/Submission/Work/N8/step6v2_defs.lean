import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.step6_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared vocabulary for `Work.N8.step6_q0_bound_v2` (the `200·L` variant of Step 6)

The variant `step6_q0_bound_v2` has the geometric hypothesis with `200 * L` in place of
`100 * L` (the constant actually produced by the `ADI`/`global_structure` pipeline, where the
swap `v/u ≤ 2` costs a factor `2`).  All the constants of the step have to be rescaled:
the window constant has to dominate `2000·ℓ·2^ℓ` instead of `1000·ℓ·2^ℓ`, and the surviving
multiplicity `2` per continuation is absorbed into the constant of the walk upper bound.

* `step6C0v2 ℓ = max 1 (4000·ℓ·2^ℓ)`: the window constant fed to the counting hypothesis;
* `step6Wv2 ℓ = 4^ℓ · step6C0v2 ℓ`: the constant of the walk upper bound;
* `step6Tuple1`, `step6Tuple2`: the two tuples of primes read along a closed walk;
* `step6S ℓ P N C₀ m q`: exactly the set of pairs of `ℓ`-tuples of primes counted by the
  hypothesis `hN4`.
-/

namespace Work.N8

open Finset

/-- The window constant `C₀(ℓ) = max 1 (4000·ℓ·2^ℓ)` of the `200·L` variant. -/
noncomputable def step6C0v2 (ℓ : ℕ) : ℝ := max 1 (4000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ)

lemma one_le_step6C0v2 (ℓ : ℕ) : 1 ≤ step6C0v2 ℓ := le_max_left _ _

lemma step6C0v2_pos (ℓ : ℕ) : 0 < step6C0v2 ℓ := lt_of_lt_of_le one_pos (one_le_step6C0v2 ℓ)

lemma le_step6C0v2 (ℓ : ℕ) : 4000 * (ℓ : ℝ) * (2 : ℝ) ^ ℓ ≤ step6C0v2 ℓ := le_max_right _ _

/-- The constant of the walk upper bound: `4^ℓ · C₀(ℓ)`.  The factor `4^ℓ` absorbs the
`2^ℓ` possible continuations of the position and the `2^ℓ` slack in the window constant. -/
noncomputable def step6Wv2 (ℓ : ℕ) : ℝ := (4 : ℝ) ^ ℓ * step6C0v2 ℓ

lemma step6Wv2_pos (ℓ : ℕ) : 0 < step6Wv2 ℓ :=
  mul_pos (by positivity) (step6C0v2_pos ℓ)

lemma one_le_step6Wv2 (ℓ : ℕ) : 1 ≤ step6Wv2 ℓ := by
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (4 : ℝ) ^ ℓ * step6C0v2 ℓ := mul_le_mul h4 (one_le_step6C0v2 ℓ) (by norm_num) (by positivity)
    _ = step6Wv2 ℓ := rfl

lemma le_step6Wv2 (ℓ : ℕ) : step6C0v2 ℓ ≤ step6Wv2 ℓ := by
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ ℓ := one_le_pow₀ (by norm_num)
  calc step6C0v2 ℓ = 1 * step6C0v2 ℓ := by ring
    _ ≤ (4 : ℝ) ^ ℓ * step6C0v2 ℓ := mul_le_mul_of_nonneg_right h4 (le_of_lt (step6C0v2_pos ℓ))
    _ = step6Wv2 ℓ := rfl

/-- The tuple of first components of the edge labels read along a closed walk `w`. -/
def step6Tuple1 {V : Type} (ℓ : ℕ) (pr : V → V → ℕ × ℕ) (w : Fin ℓ → V) : Fin ℓ → ℕ :=
  fun j => (pr (w j) (w (step6next ℓ j))).1

/-- The tuple of second components of the edge labels read along a closed walk `w`. -/
def step6Tuple2 {V : Type} (ℓ : ℕ) (pr : V → V → ℕ × ℕ) (w : Fin ℓ → V) : Fin ℓ → ℕ :=
  fun j => (pr (w j) (w (step6next ℓ j))).2

/-- The set of pairs of `ℓ`-tuples of primes counted by the hypothesis `hN4` for exponent `m`
and modulus `q`: all entries prime in `[P, 2P]` and coprime to `q`, the products close within
`C₀·P^ℓ/N`, and the `m`-th powers congruent mod `q`. -/
noncomputable def step6S (ℓ : ℕ) (P N C₀ : ℝ) (m q : ℕ) :
    Finset ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) :=
  (((Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter
        (fun p ↦ ¬ p ∣ q)) ×ˢ
    (Fintype.piFinset fun _ : Fin ℓ ↦ (Work.BMF.primesIn P (2 * P)).filter
        (fun p ↦ ¬ p ∣ q))).filter
    (fun v ↦ |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
      (∏ i, v.2 i) ^ m ≡ (∏ i, v.1 i) ^ m [MOD q]))

/-- The cardinality of `step6S` as a real number.  Keeping the counting set behind this
definition avoids unfolding the large `Finset` expression in statements. -/
noncomputable def step6Scard (ℓ : ℕ) (P N C₀ : ℝ) (m q : ℕ) : ℝ :=
  ((step6S ℓ P N C₀ m q).card : ℝ)

end Work.N8
