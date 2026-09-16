import Mathlib
open scoped BigOperators

/-!
# Step L62: main2_case1_j1 sub-lemmas — S3 (the three-sum fold) committed

The CASE-1 j = 1 splice's hid needs the fold ζ + A + B + C = 0 (the guarded
zeta_214_reindexed form) into the single signed sum over the combined member family
(PLAN SESSION 205, S3).  This module commits the two generic K-level folds (all
sorry-free, AddCommGroup):
  ★ eq_neg_add_add_add (z A B C) (h : z + A + B + C = 0) : z = -A + -B + -C
      — eq_neg_of_add_eq_zero_left after reassociating, then abel;
  ★ neg_sum_sum_type (x₁ x₂ x₃) :
      -(∑ x₁) + -(∑ x₂) + -(∑ x₃) = ∑ over (ι₁ ⊕ ι₂ ⊕ ι₃) of the negated match
      — Fintype.sum_sum_type twice + Finset.sum_neg_distrib + abel.
In main2_case1_j1 these fold the rel into ζ(s) = Σ_{i₀≠u ⊕ type2 ⊕ type3}
(−a)·ζ(member); per-summand the sign is neg_coe_mul_zeta (StepL61), the a-side
guarded sum becomes the subtype sum via sum_guarded_subtype (StepL61), and the
member tuples/coefficients are the Q.c / Q.a data of the prop212_step1 package.
NEXT: main2_case1_j1 itself (statement + conversions + rcases + ι + hid via
eq_neg_add_add_add/neg_sum_sum_type + e via self/recursion + admExp_combine).
Named gates unchanged: j=0 G5 chains, m≥3 hierarchy, theorem_B/D.
-/

/-- ★ S3 core: from z + A + B + C = 0, z is the sum of the three negated terms —
the fold at the heart of main2_case1_j1's hid. -/
lemma eq_neg_add_add_add {K : Type} [AddCommGroup K] (z A B C : K) (h : z + A + B + C = 0) :
    z = -A + -B + -C := by
  have h' : z + (A + B + C) = 0 := by simpa [add_assoc] using h
  have hz : z = -(A + B + C) := eq_neg_of_add_eq_zero_left h'
  rw [hz]
  abel
open scoped BigOperators
/-- ★ S3 assembly: the negated three sums equal the single sum over the sum-type. -/
lemma neg_sum_sum_type {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    {K : Type} [AddCommGroup K] (x₁ : ι₁ → K) (x₂ : ι₂ → K) (x₃ : ι₃ → K) :
    -(∑ i : ι₁, x₁ i) + -(∑ i : ι₂, x₂ i) + -(∑ i : ι₃, x₃ i) =
      ∑ p : ι₁ ⊕ ι₂ ⊕ ι₃, (match p with
        | Sum.inl a => -x₁ a | Sum.inr (Sum.inl b) => -x₂ b | Sum.inr (Sum.inr c) => -x₃ c) := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_sum_type]
  simp [Finset.sum_neg_distrib]
  abel
