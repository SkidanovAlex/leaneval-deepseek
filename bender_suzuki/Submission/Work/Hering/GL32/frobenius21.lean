import Mathlib
import Submission.Work.Hering.Basic
import Submission.Work.Hering.GL32.inf_zpowers_eq_bot_of_coprime
import Submission.Work.Hering.GL32.fixed_point_free_zpowers
import Submission.Work.Hering.GL32.mem_normalizer_zpowers_of_zpowers_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A Frobenius group of order `21` inside `GL(3, 2)`

The group `GL(3, 2) = MulAut (Multiplicative (Fin 3 → ZMod 2))` is the automorphism group of the
`𝔽₂`-vector space `𝔽₂³ ≅ 𝔽₈`.  We exhibit

* `e7`, the multiplication by a root `α` of `X³ + X + 1` (a Singer cycle generator of order `7`);
* `e3`, the Frobenius map `x ↦ x²` of `𝔽₈`, of order `3`;

and prove that `⟨e7⟩` (of order `7`) and `⟨e3⟩` (of order `3`) form a Frobenius group of order
`21`: `⟨e3⟩` normalises `⟨e7⟩`, the two subgroups meet trivially, and every nontrivial element
of `⟨e3⟩` acts on `⟨e7⟩` without non-trivial fixed points.

Concretely, on coordinates `(v₀, v₁, v₂)` of `𝔽₂³`:

* `e7 (v₀, v₁, v₂) = (v₂, v₀ + v₂, v₁)` — the companion matrix of `X³ + X + 1`;
* `e3 (v₀, v₁, v₂) = (v₀, v₂, v₁ + v₂)` — the Frobenius map.

All the concrete verifications (`e7 ^ 7 = 1`, `e3 ^ 3 = 1`, `e3 * e7 * e3⁻¹ = e7 ^ 2`, and the
non-triviality of `e7` and `e3`) are finite computations over `ZMod 2`, discharged by `decide`.
-/

set_option autoImplicit false

namespace Work.Hering.GL32

/-- The `𝔽₂`-vector space `𝔽₂³`, written as `Fin 3 → ZMod 2`. -/
abbrev F2cube := Fin 3 → ZMod 2

/-- Multiplication by a root `α` of `X³ + X + 1` over `𝔽₂` (a Singer cycle generator of order
`7`): `v ↦ (v₂, v₀ + v₂, v₁)`. -/
def s7 : F2cube → F2cube := fun v => ![v 2, v 0 + v 2, v 1]

/-- The inverse of `s7`, namely multiplication by `α⁻¹ = α⁶`: `v ↦ (v₀ + v₁, v₂, v₀)`. -/
def s7i : F2cube → F2cube := fun v => ![v 0 + v 1, v 2, v 0]

/-- The Frobenius map `x ↦ x²` of `𝔽₈ ≅ 𝔽₂³`, of order `3`: `v ↦ (v₀, v₂, v₁ + v₂)`. -/
def s3 : F2cube → F2cube := fun v => ![v 0, v 2, v 1 + v 2]

/-- The inverse of `s3`, namely `s3 ^ 2`: `v ↦ (v₀, v₁ + v₂, v₁)`. -/
def s3i : F2cube → F2cube := fun v => ![v 0, v 1 + v 2, v 1]

/-- The element `e7` of order `7` of `GL(3, 2)`. -/
noncomputable def e7 : MulAut (Multiplicative F2cube) where
  toFun x := Multiplicative.ofAdd (s7 x.toAdd)
  invFun x := Multiplicative.ofAdd (s7i x.toAdd)
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide
  map_mul' := by intro x y; revert x y; decide

/-- The element `e3` of order `3` of `GL(3, 2)` normalising `⟨e7⟩`. -/
noncomputable def e3 : MulAut (Multiplicative F2cube) where
  toFun x := Multiplicative.ofAdd (s3 x.toAdd)
  invFun x := Multiplicative.ofAdd (s3i x.toAdd)
  left_inv := by intro x; revert x; decide
  right_inv := by intro x; revert x; decide
  map_mul' := by intro x y; revert x y; decide

/-- `e7` has order `7`. -/
lemma e7_pow_seven : e7 ^ 7 = 1 := by
  apply MulEquiv.ext; decide

/-- `e3` has order `3`. -/
lemma e3_pow_three : e3 ^ 3 = 1 := by
  apply MulEquiv.ext; decide

/-- The Frobenius map conjugates multiplication by `α` into multiplication by `α²`. -/
lemma e3_conj_e7 : e3 * e7 * e3⁻¹ = e7 ^ 2 := by
  apply MulEquiv.ext; decide

/-- `e7` is not the identity. -/
lemma e7_ne_one : e7 ≠ 1 := by decide

/-- `e3` is not the identity. -/
lemma e3_ne_one : e3 ≠ 1 := by decide

/-- `⟨e7²⟩ = ⟨e7⟩` (because `e7` has order `7` and `2` is invertible mod `7`). -/
lemma zpowers_e7_sq : Subgroup.zpowers (e7 ^ 2) = Subgroup.zpowers e7 := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers_iff.mpr ⟨2, by decide⟩
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_zpowers_iff.mpr ⟨4, by decide⟩

theorem frobenius21 :
    ∃ S X : Subgroup (MulAut (Multiplicative (Fin 3 → ZMod 2))),
      Nat.card S = 7 ∧ Nat.card X = 3 ∧
      X ≤ Subgroup.normalizer (S : Set (MulAut (Multiplicative (Fin 3 → ZMod 2)))) ∧
      S ⊓ X = ⊥ ∧ (∀ x ∈ X, x ≠ 1 → ∀ s ∈ S, x * s * x⁻¹ = s → s = 1) := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨Subgroup.zpowers e7, Subgroup.zpowers e3, ?_, ?_, ?_, ?_, ?_⟩
  · -- `⟨e7⟩` has order `7`
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hp := h7) e7_pow_seven e7_ne_one
  · -- `⟨e3⟩` has order `3`
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime e3_pow_three e3_ne_one
  · -- `⟨e3⟩` normalises `⟨e7⟩`
    refine Subgroup.zpowers_le.mpr ?_
    refine mem_normalizer_zpowers_of_zpowers_conj e7 e3 ?_
    rw [e3_conj_e7]
    exact zpowers_e7_sq
  · -- the two subgroups meet trivially
    exact inf_zpowers_eq_bot_of_coprime e7 e3 e7_pow_seven e3_pow_three (by decide)
  · -- every nontrivial element of `⟨e3⟩` is fixed-point-free on `⟨e7⟩`
    exact fixed_point_free_zpowers e7 e3 e7_pow_seven e3_pow_three e3_conj_e7

end Work.Hering.GL32
