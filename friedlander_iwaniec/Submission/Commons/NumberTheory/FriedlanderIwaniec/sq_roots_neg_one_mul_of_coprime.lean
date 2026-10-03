import Mathlib.Data.ZMod.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Set

/-- A ring equivalence carries the set of square roots of `-1` onto the
corresponding set in the target ring. -/
lemma ringEquiv_image_sq_neg_one {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    e '' ({r : R | r ^ 2 = -1} : Set R) = {s : S | s ^ 2 = -1} := by
  ext s
  constructor
  · rintro ⟨r, hr, rfl⟩
    change (e r) ^ 2 = -1
    rw [← RingEquiv.map_pow e r 2, hr, RingEquiv.map_neg_one]
  · intro hs
    change s ^ 2 = -1 at hs
    refine ⟨e.symm s, ?_, ?_⟩
    · change (e.symm s) ^ 2 = -1
      rw [← RingEquiv.map_pow (RingEquiv.symm e) s 2, hs, RingEquiv.map_neg_one]
    · exact e.apply_symm_apply s

/-- In a product ring, squaring and negating happen componentwise, so a pair
squares to `-1` exactly when both components do. -/
lemma sq_neg_one_prod {R S : Type*} [Ring R] [Ring S] (p : R × S) :
    (p ^ 2 = -1) ↔ p.1 ^ 2 = -1 ∧ p.2 ^ 2 = -1 := by
  constructor
  · intro hp
    constructor
    · have h1 := congrArg Prod.fst hp
      simpa [pow_two] using h1
    · have h2 := congrArg Prod.snd hp
      simpa [pow_two] using h2
  · rintro ⟨h1, h2⟩
    apply Prod.ext
    · simpa [pow_two] using h1
    · simpa [pow_two] using h2

/-- The number of square roots of `-1` modulo `m * n` is the product of the
number of square roots of `-1` modulo `m` and modulo `n`, for coprime moduli.

This is the Chinese remainder theorem: `ZMod (m * n) ≃ ZMod m × ZMod n`
carries the solution set of `x ^ 2 = -1` bijectively onto the Cartesian
product of the two solution sets, and `Set.ncard` respects products. -/
theorem sq_roots_neg_one_mul_of_coprime {m n : ℕ} (hcop : Nat.Coprime m n) :
    ({α : ZMod (m * n) | α ^ 2 = -1}.ncard) =
      ({α : ZMod m | α ^ 2 = -1}.ncard) * ({α : ZMod n | α ^ 2 = -1}.ncard) := by
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  have himg : e '' ({α : ZMod (m * n) | α ^ 2 = -1} : Set (ZMod (m * n))) =
      {p : ZMod m × ZMod n | p ^ 2 = -1} := ringEquiv_image_sq_neg_one e
  have hB : ({p : ZMod m × ZMod n | p ^ 2 = -1} : Set (ZMod m × ZMod n)) =
      ({α : ZMod m | α ^ 2 = -1} ×ˢ {α : ZMod n | α ^ 2 = -1}) := by
    ext p
    change p ^ 2 = -1 ↔ p.1 ^ 2 = -1 ∧ p.2 ^ 2 = -1
    exact sq_neg_one_prod p
  calc
    ({α : ZMod (m * n) | α ^ 2 = -1}.ncard)
        = (e '' ({α : ZMod (m * n) | α ^ 2 = -1} : Set (ZMod (m * n)))).ncard := by
          exact (Set.ncard_image_of_injective _ e.injective).symm
    _ = ({p : ZMod m × ZMod n | p ^ 2 = -1} : Set (ZMod m × ZMod n)).ncard := by rw [himg]
    _ = (({α : ZMod m | α ^ 2 = -1} ×ˢ {α : ZMod n | α ^ 2 = -1}) : Set (ZMod m × ZMod n)).ncard := by
          rw [hB]
    _ = ({α : ZMod m | α ^ 2 = -1}.ncard) * ({α : ZMod n | α ^ 2 = -1}.ncard) := by
          exact Set.ncard_prod

end Commons.NumberTheory.FriedlanderIwaniec