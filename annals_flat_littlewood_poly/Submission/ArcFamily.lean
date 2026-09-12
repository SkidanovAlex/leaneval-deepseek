import Mathlib

/-! Interval-family interface shared by Section 3 (output: bad intervals of the
cosine polynomial `c`) and Section 5 (input: interval family over which the odd
sine polynomial `s_o` must be large).

Since `c(θ)` is π-periodic and symmetric under `θ ↦ π ± θ`, and every odd sine
sum `Σ_j ε_j sin(jθ)` has the same symmetry group acting on its modulus, all
the analysis can be carried out on the fundamental quadrant `[0, π/2]`.  We
therefore model a family of `N` pairwise-separated grid intervals lying inside
`(100π/n, π/2 − 100π/n)`:

    I_i := [ p_i·π/n , q_i·π/n ],   0 ≤ p_i < q_i,
    length ≤ 6π/n  (q_i − p_i ≤ 6),
    far from 0 and π/2 (p_i ≥ 100, 2 q_i + 200 ≤ n),
    pairwise grid-distance ≥ π/n (integer-disjointness suffices).

The full-circle family is the orbit of this family under `θ ↦ π±θ` (4N
intervals); Section 5 needs only the quadrant part. -/

noncomputable section
open scoped BigOperators

set_option autoImplicit false

namespace Submission
namespace Family

/-- A grid interval `[p·π/n, q·π/n]` with integer endpoints `0 ≤ p < q`. -/
structure Grid (n : ℕ) where
  p : ℤ
  q : ℤ
  hp_nonneg : 0 ≤ p
  hlt : p < q

namespace Grid

/-- Left endpoint `p·π/n`. -/
def lo {n : ℕ} (a : Grid n) : ℝ := (a.p : ℝ) * Real.pi / (n : ℝ)

/-- Right endpoint `q·π/n`. -/
def hi {n : ℕ} (a : Grid n) : ℝ := (a.q : ℝ) * Real.pi / (n : ℝ)

/-- The closed real interval `[lo, hi]`. -/
def toSet {n : ℕ} (a : Grid n) : Set ℝ := Set.Icc (lo a) (hi a)

lemma lo_le_hi {n : ℕ} (a : Grid n) : lo a ≤ hi a := by
  unfold lo hi
  have hq : (a.p : ℝ) ≤ (a.q : ℝ) := by exact_mod_cast le_of_lt a.hlt
  have hqpi : (a.p : ℝ) * Real.pi ≤ (a.q : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right hq Real.pi_pos.le
  exact div_le_div_of_nonneg_right hqpi (by positivity)

/-- Length of the interval (in grid units, ≤ 6 by the family axioms). -/
def len {n : ℕ} (a : Grid n) : ℤ := a.q - a.p

/-- Length is `(len)·π/n`. -/
lemma hi_sub_lo {n : ℕ} (a : Grid n) (hn : n ≠ 0) :
    hi a - lo a = (a.len : ℝ) * Real.pi / (n : ℝ) := by
  unfold hi lo len
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  norm_num [len, sub_eq_add_neg]
  field_simp [hn0]

end Grid

/-- A suitable quadrant family: `N` distinct grid intervals in the first
quadrant, short, mutually separated, and at distance ≥ 100π/n from `0` and
`π/2`.  (`inj` guarantees distinctness of the enumeration.) -/
structure Quad (n N : ℕ) where
  arc : Fin N → Grid n
  inj : Function.Injective arc
  len_le : ∀ i : Fin N, (arc i).len ≤ 6
  far_left : ∀ i : Fin N, 100 ≤ (arc i).p
  far_right : ∀ i : Fin N, 2 * (arc i).q + 200 ≤ (n : ℤ)
  sep : ∀ ⦃i j : Fin N⦄, i ≠ j → (arc i).q < (arc j).p ∨ (arc j).q < (arc i).p

namespace Quad

/-- Union of the intervals of a family (a subset of `ℝ`). -/
def union {n N : ℕ} (F : Quad n N) : Set ℝ :=
  {x : ℝ | ∃ i : Fin N, x ∈ (F.arc i).toSet}

lemma mem_union {n N : ℕ} (F : Quad n N) (x : ℝ) :
    x ∈ union F ↔ ∃ i : Fin N, x ∈ (F.arc i).toSet := Iff.rfl

/-- A point is in the union iff it lies in some arc's interval. -/
lemma union_def {n N : ℕ} (F : Quad n N) (x : ℝ) :
    x ∈ F.union ↔ ∃ i : Fin N, (F.arc i).lo ≤ x ∧ x ≤ (F.arc i).hi := by
  rw [mem_union]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, hi⟩

end Quad
end Family
end Submission
