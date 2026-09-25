import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

/-!
# The Chinese-remainder / sumset identity for the torsion arcs `Σ_{⊆}` (Tao, §4)

For a finite set `S` of pairwise coprime integers and `A ⊆ S`, `Σ_{⊆ A} = 𝕋[Q_A]` is the
`Q_A`-torsion subgroup of the circle, `Q_A = ∏_{q ∈ A} q` (`ArcDefs.lean`).  This file proves the
additivity of `Σ_{⊆ ·}` over disjoint, cross-coprime sets:

`Σ_{⊆ A} + Σ_{⊆ B} = Σ_{⊆ A ∪ B}`,   i.e.   `𝕋[Q_A] + 𝕋[Q_B] = 𝕋[Q_A Q_B]`.

The substantive direction is the Bézout step: with `gcd(Q_A, Q_B) = 1`, integers `u, v` satisfy
`u Q_A + v Q_B = 1`, so `a/(Q_A Q_B) = (a v)/Q_A + (a u)/Q_B` splits a point of `Σ_{⊆ A ∪ B}` as a
sum of a point of `Σ_{⊆ A}` and a point of `Σ_{⊆ B}`.

Degenerate note.  `Σ_{⊆ C} = {0}` whenever `Q_C = 0` (i.e. `0 ∈ C`) or `Q_C = 1`.  In the case
`0 ∈ A`, cross-coprimality forces every element of `B` to equal `1` (since `gcd(0, q') = q' = 1`),
hence `Q_B = 1`; the identity then reads `{0} + {0} = {0}` and still holds.  The main case is
therefore `0 ∉ A ∪ B`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The arithmetic of the arc points -/

/-- `arcPt` is additive in the numerator: `a/Q + b/Q = (a+b)/Q`. -/
lemma arcPt_add (Q : ℕ) (a b : ℤ) : arcPt Q a + arcPt Q b = arcPt Q (a + b) := by
  rw [arcPt, arcPt, arcPt, ← AddCircle.coe_add]
  congr 1
  push_cast
  ring

/-- Adding points with two coprime denominators: `a/Q + b/R = (a R + b Q)/(Q R)` for `Q, R ≠ 0`. -/
lemma arcPt_add_denom {Q R : ℕ} (hQ : Q ≠ 0) (hR : R ≠ 0) (a b : ℤ) :
    arcPt Q a + arcPt R b = arcPt (Q * R) (a * (R : ℤ) + b * (Q : ℤ)) := by
  rw [arcPt, arcPt, arcPt, ← AddCircle.coe_add]
  congr 1
  push_cast
  field_simp

/-- `0/Q = 0`. -/
lemma arcPt_zero (Q : ℕ) : arcPt Q 0 = 0 := by
  rw [arcPt, Int.cast_zero, zero_div, AddCircle.coe_zero]

/-- An integer is the origin of the circle `𝕋 = ℝ/ℤ`. -/
lemma coe_int_circle_eq_zero (n : ℤ) : ((n : ℝ) : Circle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by rw [zsmul_eq_mul, mul_one]⟩

/-- `a/1 = 0` in the circle. -/
lemma arcPt_one (a : ℤ) : arcPt 1 a = 0 := by
  rw [arcPt, Nat.cast_one, div_one]
  exact coe_int_circle_eq_zero a

/-! ## The degenerate arcs `Q_C = 0` and `Q_C = 1` -/

/-- If `Q_C = 0` then `Σ_{⊆ C} = {0}` (the point `a/0` is `0`). -/
lemma sigmaSubA_eq_zero_of_QA_eq_zero {C : Finset ℕ} (h : QA C = 0) :
    sigmaSubA C = {0} := by
  ext x
  rw [sigmaSubA, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [h, arcPt]
    simp
  · rintro rfl
    exact ⟨0, by rw [h, arcPt]; simp⟩

/-- If `Q_C = 1` then `Σ_{⊆ C} = {0}` (the point `a/1` is `0`). -/
lemma sigmaSubA_eq_zero_of_QA_eq_one {C : Finset ℕ} (h : QA C = 1) :
    sigmaSubA C = {0} := by
  ext x
  rw [sigmaSubA, Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl⟩
    rw [h, arcPt_one]
  · rintro rfl
    exact ⟨0, by rw [h, arcPt_one]⟩

/-! ## Products of `Q` -/

/-- Cross-coprimality of `A` and `B` gives `Coprime (Q_A) (Q_B)`. -/
lemma coprime_QA_of_disjoint {A B : Finset ℕ}
    (hcop : ∀ q ∈ A, ∀ q' ∈ B, Nat.Coprime q q') : Nat.Coprime (QA A) (QA B) := by
  rw [QA, QA]
  exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.prod_right fun q' hq' => hcop q hq q' hq'

/-- `Q_{A ∪ B} = Q_A * Q_B` for disjoint `A, B`. -/
lemma QA_union {A B : Finset ℕ} (h : Disjoint A B) : QA (A ∪ B) = QA A * QA B := by
  rw [QA, QA, QA, Finset.prod_union h]

/-! ## The main theorem -/

/-- **Chinese remainder / sumset identity for the torsion arcs**, the `Σ_{⊆}` case of Tao's (sigma) (arXiv:2008.05066, §4): if `A, B` are disjoint sets of pairwise coprime integers then `Σ_{⊆ A} + Σ_{⊆ B} = Σ_{⊆ A ∪ B}`, i.e. `𝕋[Q_A] + 𝕋[Q_B] = 𝕋[Q_A Q_B]`.  Proof: one inclusion is immediate; for the other, Bézout for the coprime integers `Q_A`, `Q_B` writes `x = u Q_A x + v Q_B x` with `v Q_B x ∈ 𝕋[Q_A]` and `u Q_A x ∈ 𝕋[Q_B]`. -/
theorem sigmaSubA_add (A B : Finset ℕ) (hdisj : Disjoint A B)
    (hcop : ∀ q ∈ A, ∀ q' ∈ B, Nat.Coprime q q') (x : Work.BourgainPlan.IonescuWainger.Circle) :
    x ∈ Work.BourgainPlan.IonescuWainger.sigmaSubA (A ∪ B) ↔
      ∃ y ∈ Work.BourgainPlan.IonescuWainger.sigmaSubA A,
        ∃ z ∈ Work.BourgainPlan.IonescuWainger.sigmaSubA B, y + z = x := by
  by_cases h0 : (0 : ℕ) ∈ A ∪ B
  · -- Degenerate case: `0 ∈ A ∪ B`.  Then `0` lies in one of `A`, `B`, and cross-coprimality
    -- forces the other set to consist of `1`'s, so all three arcs are `{0}`.
    have hL : sigmaSubA (A ∪ B) = {0} :=
      sigmaSubA_eq_zero_of_QA_eq_zero (Finset.prod_eq_zero h0 rfl)
    have hA : sigmaSubA A = {0} := by
      rcases Finset.mem_union.mp h0 with h | h
      · exact sigmaSubA_eq_zero_of_QA_eq_zero (Finset.prod_eq_zero h rfl)
      · exact sigmaSubA_eq_zero_of_QA_eq_one
          (Finset.prod_eq_one fun q hq => (Nat.coprime_zero_right q).mp (hcop q hq 0 h))
    have hB : sigmaSubA B = {0} := by
      rcases Finset.mem_union.mp h0 with h | h
      · exact sigmaSubA_eq_zero_of_QA_eq_one
          (Finset.prod_eq_one fun q' hq' => (Nat.coprime_zero_left q').mp (hcop 0 h q' hq'))
      · exact sigmaSubA_eq_zero_of_QA_eq_zero (Finset.prod_eq_zero h rfl)
    rw [hL, hA, hB]
    constructor
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, Set.mem_singleton 0, 0, Set.mem_singleton 0, by rw [hx, add_zero]⟩
    · rintro ⟨y, hy, z, hz, hsum⟩
      rw [Set.mem_singleton_iff] at hy hz
      rw [hy, hz, zero_add] at hsum
      rw [Set.mem_singleton_iff]
      exact hsum.symm
  · -- Main case: `0 ∉ A ∪ B`, so `Q_A, Q_B ≥ 1` and `Coprime Q_A Q_B`.
    have hA0 : ∀ q ∈ A, q ≠ 0 := fun q hq hq0 =>
      h0 (by rw [← hq0]; exact Finset.mem_union_left B hq)
    have hB0 : ∀ q ∈ B, q ≠ 0 := fun q hq hq0 =>
      h0 (by rw [← hq0]; exact Finset.mem_union_right A hq)
    have hQA : QA A ≠ 0 := Finset.prod_ne_zero_iff.mpr hA0
    have hQB : QA B ≠ 0 := Finset.prod_ne_zero_iff.mpr hB0
    have hQU : QA (A ∪ B) = QA A * QA B := QA_union hdisj
    have hcopAB : Nat.Coprime (QA A) (QA B) := coprime_QA_of_disjoint hcop
    constructor
    · -- `Σ_{⊆ A ∪ B} ⊆ Σ_{⊆ A} + Σ_{⊆ B}`: Bézout splits `a/(Q_A Q_B)`.
      rintro ⟨a, rfl⟩
      rw [hQU]
      obtain ⟨u, v, huv⟩ := hcopAB.isCoprime
      refine ⟨arcPt (QA A) (a * v), ⟨a * v, rfl⟩, arcPt (QA B) (a * u), ⟨a * u, rfl⟩, ?_⟩
      rw [arcPt_add_denom hQA hQB]
      congr 1
      have h1 : (a * v) * (QA B : ℤ) + (a * u) * (QA A : ℤ)
          = a * (u * (QA A : ℤ) + v * (QA B : ℤ)) := by ring
      rw [h1, huv, mul_one]
    · -- `Σ_{⊆ A} + Σ_{⊆ B} ⊆ Σ_{⊆ A ∪ B}`: put the two fractions over the common denominator.
      rintro ⟨y, hy, z, hz, hsum⟩
      obtain ⟨b, hb⟩ := hy
      obtain ⟨c, hc⟩ := hz
      rw [← hb, ← hc] at hsum
      rw [← hsum]
      rw [show sigmaSubA (A ∪ B) = Set.range (arcPt (QA A * QA B)) from by rw [sigmaSubA, hQU]]
      exact ⟨b * (QA B : ℤ) + c * (QA A : ℤ), (arcPt_add_denom hQA hQB b c).symm⟩

end Work.BourgainPlan.IonescuWainger
