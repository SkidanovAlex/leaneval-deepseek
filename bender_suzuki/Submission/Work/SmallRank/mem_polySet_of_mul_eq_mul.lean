import Mathlib
import Submission.Work.SmallRank.GL2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.SmallRank

open Matrix

/-- A `2 × 2` matrix is scalar iff its off-diagonal entries vanish and its two diagonal entries
agree. -/
lemma isScalar_iff {p : ℕ} (a : M2 p) :
    IsScalar a ↔ a 0 1 = 0 ∧ a 1 0 = 0 ∧ a 0 0 = a 1 1 := by
  constructor
  · rintro ⟨α, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.smul_apply]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨a 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, h1, h2, h3]

/-- A matrix is non-scalar iff it has a non-vanishing off-diagonal entry, or distinct diagonal
entries. -/
lemma nonScalar_iff {p : ℕ} (a : M2 p) :
    NonScalar a ↔ a 0 1 ≠ 0 ∨ a 1 0 ≠ 0 ∨ a 0 0 ≠ a 1 1 := by
  rw [NonScalar, isScalar_iff]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    exact h ⟨hc.1, hc.2.1, hc.2.2⟩
  · rintro (h1 | h2 | h3) ⟨e1, e2, e3⟩
    · exact h1 e1
    · exact h2 e2
    · exact h3 e3

/-- The four entrywise equations coming from `x * a = a * x`. -/
lemma mul_eq_mul_entries {p : ℕ} {a x : M2 p} (h : x * a = a * x) :
    (x 0 0 * a 0 0 + x 0 1 * a 1 0 = a 0 0 * x 0 0 + a 0 1 * x 1 0) ∧
    (x 0 0 * a 0 1 + x 0 1 * a 1 1 = a 0 0 * x 0 1 + a 0 1 * x 1 1) ∧
    (x 1 0 * a 0 0 + x 1 1 * a 1 0 = a 1 0 * x 0 0 + a 1 1 * x 1 0) ∧
    (x 1 0 * a 0 1 + x 1 1 * a 1 1 = a 1 0 * x 0 1 + a 1 1 * x 1 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  · have hh := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  · have hh := congrFun (congrFun h 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh
  · have hh := congrFun (congrFun h 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using hh

/-- Case `a 0 1 ≠ 0` of the centraliser computation: solve for `β` from the `(0,1)` entry. -/
lemma mem_polySet_of_a01_ne {p : ℕ} [Fact p.Prime] {a x : M2 p}
    (h00 : x 0 0 * a 0 0 + x 0 1 * a 1 0 = a 0 0 * x 0 0 + a 0 1 * x 1 0)
    (h01 : x 0 0 * a 0 1 + x 0 1 * a 1 1 = a 0 0 * x 0 1 + a 0 1 * x 1 1)
    (ha01 : a 0 1 ≠ 0) : x ∈ polySet a := by
  set β : ZMod p := x 0 1 * (a 0 1)⁻¹ with hβ
  set α : ZMod p := x 0 0 - β * a 0 0 with hα
  refine ⟨α, β, ?_⟩
  have hb : β * a 0 1 = x 0 1 := by rw [hβ, mul_assoc, inv_mul_cancel₀ ha01, mul_one]
  have h00' : x 0 1 * a 1 0 = a 0 1 * x 1 0 := by
    have h := h00
    rw [mul_comm (x 0 0) (a 0 0)] at h
    exact add_left_cancel h
  have h01' : a 0 1 * x 1 1 = x 0 0 * a 0 1 + x 0 1 * a 1 1 - a 0 0 * x 0 1 := by
    linear_combination -h01
  have e10 : x 1 0 = β * a 1 0 := by
    have : a 0 1 * (β * a 1 0) = a 0 1 * x 1 0 := by rw [← h00', ← hb]; ring
    exact (mul_left_cancel₀ ha01 this).symm
  have e11 : x 1 1 = α + β * a 1 1 := by
    have : a 0 1 * x 1 1 = a 0 1 * (α + β * a 1 1) := by
      rw [h01', ← hb, hα]; ring
    exact mul_left_cancel₀ ha01 this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, hb, e10, e11, hα]

/-- Case `a 0 1 = 0`, `a 1 0 ≠ 0`: solve for `β` from the `(1,0)` entry. -/
lemma mem_polySet_of_a10_ne {p : ℕ} [Fact p.Prime] {a x : M2 p}
    (h00 : x 0 0 * a 0 0 + x 0 1 * a 1 0 = a 0 0 * x 0 0 + a 0 1 * x 1 0)
    (h10 : x 1 0 * a 0 0 + x 1 1 * a 1 0 = a 1 0 * x 0 0 + a 1 1 * x 1 0)
    (ha01v : a 0 1 = 0) (ha10 : a 1 0 ≠ 0) : x ∈ polySet a := by
  set β : ZMod p := x 1 0 * (a 1 0)⁻¹ with hβ
  set α : ZMod p := x 0 0 - β * a 0 0 with hα
  refine ⟨α, β, ?_⟩
  have hb : β * a 1 0 = x 1 0 := by rw [hβ, mul_assoc, inv_mul_cancel₀ ha10, mul_one]
  have h00' : x 0 1 * a 1 0 = 0 := by
    have h := h00
    rw [ha01v, zero_mul, add_zero] at h
    linear_combination h
  have hx01 : x 0 1 = 0 := (mul_eq_zero.mp h00').resolve_right ha10
  have h10' : a 1 0 * x 1 1 = a 1 0 * x 0 0 + a 1 1 * x 1 0 - x 1 0 * a 0 0 := by
    linear_combination h10
  have e11 : x 1 1 = α + β * a 1 1 := by
    have : a 1 0 * x 1 1 = a 1 0 * (α + β * a 1 1) := by
      rw [h10', ← hb, hα]; ring
    exact mul_left_cancel₀ ha10 this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, Matrix.smul_apply, hx01, ha01v, hb, e11, hα]

/-- Case `a` is diagonal with distinct diagonal entries: then `x` is diagonal too and is a
polynomial in `a`. -/
lemma mem_polySet_of_diag_ne {p : ℕ} [Fact p.Prime] {a x : M2 p}
    (h01 : x 0 0 * a 0 1 + x 0 1 * a 1 1 = a 0 0 * x 0 1 + a 0 1 * x 1 1)
    (h10 : x 1 0 * a 0 0 + x 1 1 * a 1 0 = a 1 0 * x 0 0 + a 1 1 * x 1 0)
    (ha01v : a 0 1 = 0) (ha10v : a 1 0 = 0) (ha00 : a 0 0 ≠ a 1 1) : x ∈ polySet a := by
  set β : ZMod p := (x 1 1 - x 0 0) * (a 1 1 - a 0 0)⁻¹ with hβ
  set α : ZMod p := x 0 0 - β * a 0 0 with hα
  refine ⟨α, β, ?_⟩
  have hsub : a 1 1 - a 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha00)
  have hb : β * (a 1 1 - a 0 0) = x 1 1 - x 0 0 := by
    rw [hβ, mul_assoc, inv_mul_cancel₀ hsub, mul_one]
  have h01' : x 0 1 * (a 1 1 - a 0 0) = 0 := by
    have h := h01
    simp only [ha01v, mul_zero, zero_mul, add_zero, zero_add] at h
    linear_combination h
  have hx01 : x 0 1 = 0 := (mul_eq_zero.mp h01').resolve_right hsub
  have h10' : x 1 0 * (a 0 0 - a 1 1) = 0 := by
    have h := h10
    simp only [ha10v, mul_zero, zero_mul, add_zero, zero_add] at h
    linear_combination h
  have hx10 : x 1 0 = 0 := (mul_eq_zero.mp h10').resolve_right (sub_ne_zero.mpr ha00)
  have e11 : x 1 1 = α + β * a 1 1 := by
    rw [hα]
    linear_combination -hb
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, hx01, hx10, ha01v, ha10v, hα, e11]

/-- The centraliser in `M₂(𝔽_p)` of a non-scalar matrix `a` is the commutative algebra
`polySet a = 𝔽_p[a]` spanned by `1` and `a`. -/
theorem mem_polySet_of_mul_eq_mul {p : ℕ} [Fact p.Prime] {a x : M2 p} (ha : NonScalar a)
    (h : x * a = a * x) : x ∈ polySet a := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_eq_mul_entries h
  rcases (nonScalar_iff a).mp ha with h1 | h1 | h1
  · exact mem_polySet_of_a01_ne h00 h01 h1
  · by_cases h01z : a 0 1 = 0
    · exact mem_polySet_of_a10_ne h00 h10 h01z h1
    · exact mem_polySet_of_a01_ne h00 h01 h01z
  · by_cases h01z : a 0 1 = 0
    · by_cases h10z : a 1 0 = 0
      · exact mem_polySet_of_diag_ne h01 h10 h01z h10z h1
      · exact mem_polySet_of_a10_ne h00 h10 h01z h10z
    · exact mem_polySet_of_a01_ne h00 h01 h01z

end Work.SmallRank
