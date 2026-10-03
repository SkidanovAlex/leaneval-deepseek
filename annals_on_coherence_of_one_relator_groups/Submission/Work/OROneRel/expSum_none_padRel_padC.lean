import Mathlib
import Submission.Work.OROneRel.padDefs

/-!
# The padding letter has exponent sum zero in the padded relator

Given a relator `r : FreeGroup α`, two distinct letters `x ≠ t`, and the padding exponents
`padC r x t` (supported on `{x,t}`, with `c x = σ_t r` and `c t = -σ_x r`), we prove that the fresh
padding letter `none` has zero exponent sum in `padRel (padC r x t) r`.

The two ingredients are

* `expSum_none_padHom_apply` : the exponent sum of the padding letter in `padHom c w` is the
  `c`-weighted exponent sum `Σ_a c a · σ_a w`, realised as the lift
  `FreeGroup.lift (fun a => Multiplicative.ofAdd (c a))`;
* `lift_ofAdd_padC_eq_hom` : for the specific `padC`, that lift is the product of the two power maps
  `σ_x ↦ (σ_x r)^(σ_t r)` and `σ_t ↦ (σ_t r)^(-σ_x r)`.

Both are proved here from scratch, so this file rests on no unproved input.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The exponent sum of a generator -/

/-- The exponent sum of a generator that is not the chosen letter. -/
theorem expSum_generator_ne {β : Type*} {s a : β} (h : a ≠ s) :
    expSum s (FreeGroup.of a) = 1 := by
  rw [expSum, FreeGroup.lift_apply_of]
  simp [h]

/-- The exponent sum of the chosen generator. -/
theorem expSum_generator_eq {β : Type*} (s : β) :
    expSum s (FreeGroup.of s) = Multiplicative.ofAdd (1 : ℤ) := by
  rw [expSum, FreeGroup.lift_apply_of]
  simp

/-- An integral power of the multiplicative unit `ofAdd 1` of `Multiplicative ℤ`. -/
theorem one_zpow_ofAdd_one (n : ℤ) :
    (Multiplicative.ofAdd (1 : ℤ)) ^ n = Multiplicative.ofAdd n := by
  rw [← ofAdd_zsmul, zsmul_one]
  simp

/-! ### The exponent sum of the padding letter -/

/-- The exponent sum of the padding letter in a padded word is the `c`-weighted exponent sum. -/
theorem expSum_none_padHom_apply (c : α → ℤ) (w : FreeGroup α) :
    expSum (none : PadT α) (padHom c w) =
      FreeGroup.lift (fun a : α => Multiplicative.ofAdd (c a)) w := by
  classical
  have h : (expSum (none : PadT α)).comp (padHom c) =
      FreeGroup.lift (fun a : α => Multiplicative.ofAdd (c a)) := by
    apply FreeGroup.ext_hom
    intro a
    simp only [MonoidHom.comp_apply]
    rw [padHom_of, padGen, FreeGroup.lift_apply_of]
    rw [map_mul, map_mul, map_zpow]
    rw [expSum_generator_ne (s := (none : PadT α)) (a := some a) (by simp),
      expSum_generator_eq (none : PadT α)]
    simp [one_zpow_ofAdd_one]
  exact DFunLike.congr_fun h w

/-! ### The values of the padding exponents `padC` -/

/-- The value of `padC` at the first chosen letter. -/
theorem padC_apply_self_x (r : FreeGroup α) (x t : α) :
    padC r x t x = (expSum t r).toAdd := by
  rw [padC]
  simp

/-- The value of `padC` at the second chosen letter. -/
theorem padC_apply_self_t (r : FreeGroup α) {x t : α} (hxt : x ≠ t) :
    padC r x t t = -((expSum x r).toAdd) := by
  rw [padC]
  simp [show t ≠ x from fun h => hxt h.symm]

/-- The value of `padC` at any other letter. -/
theorem padC_apply_other (r : FreeGroup α) {x t a : α} (hax : a ≠ x) (hat : a ≠ t) :
    padC r x t a = 0 := by
  rw [padC]
  simp [hax, hat]

/-- For the padding exponents `padC r x t` (supported on `{x,t}`), the weighted exponent sum is a
product of two powers of the exponent sums in `x` and `t`. -/
theorem lift_ofAdd_padC_eq_hom (r : FreeGroup α) {x t : α} (hxt : x ≠ t) :
    FreeGroup.lift (fun a : α => Multiplicative.ofAdd ((padC r x t) a)) =
      (zpowGroupHom ((expSum t r).toAdd)).comp (expSum x) *
        (zpowGroupHom (-((expSum x r).toAdd))).comp (expSum t) := by
  classical
  apply FreeGroup.ext_hom
  intro a
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, zpowGroupHom_apply]
  rw [FreeGroup.lift_apply_of]
  by_cases hax : a = x
  · rw [hax]
    rw [expSum_generator_eq x, expSum_generator_ne (s := t) hxt, padC_apply_self_x r x t]
    simp [one_zpow_ofAdd_one]
  · by_cases hat : a = t
    · rw [hat]
      rw [expSum_generator_ne (s := x) (fun h : t = x => hxt h.symm), expSum_generator_eq t,
        padC_apply_self_t r hxt]
      simp [one_zpow_ofAdd_one]
    · rw [expSum_generator_ne (s := x) hax, expSum_generator_ne (s := t) hat,
        padC_apply_other r hax hat]
      simp [hax, hat]

/-! ### The target -/

theorem expSum_none_padRel_padC {α : Type u} (r : FreeGroup α) {x t : α} (hxt : x ≠ t) :
    Work.OROneRel.expSum (none : Option α)
      (Work.OROneRel.padRel (Work.OROneRel.padC r x t) r) = 1 := by
  classical
  rw [padRel, expSum_none_padHom_apply, lift_ofAdd_padC_eq_hom r hxt]
  rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, zpowGroupHom_apply,
    zpowGroupHom_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_zpow, toAdd_zpow, toAdd_one]
  simp
  ring

end Work.OROneRel
