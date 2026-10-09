/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer character is injective modulo `n`-th powers

For a finite Galois extension `L/K` and a primitive `n`-th root of unity `ζ ∈ K`, the Kummer
pairing `(σ, a) ↦ σ α / α` (where `α ^ n = a` in `Lˣ`) is injective modulo `n`-th powers: two
elements `a b` of the Kummer subgroup `Kˣ ∩ (Lˣ)^n` have the same Kummer character if and only
if `a / b` is an `n`-th power in `Kˣ`:

`kummerCharacter_eq_iff_div_mem`.

The proof is the classical one.  Writing `α = kummerRoot a`, `β = kummerRoot b`, the equality of
the characters says that `σ α / α = σ β / β` for every `σ ∈ Gal(L/K)`, i.e. that `α / β` is fixed
by `Gal(L/K)`.  Since `L/K` is Galois, `α / β` then lies in the image of `Kˣ` in `Lˣ`, say
`α / β = c` with `c ∈ Kˣ`; raising to the `n`-th power gives `a / b = c ^ n`.
Conversely, if `a / b = d ^ n` with `d ∈ Kˣ`, then `β * d` is another `n`-th root of `a`, and the
ratio `σ α / α` only depends on `α ^ n`.
-/
import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

open IntermediateField

section RatioLemmas

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- `kummerRatio` is multiplicative in its second argument. -/
lemma kummerRatio_mul_apply (σ : Gal(L/K)) (x y : Lˣ) :
    kummerRatio σ (x * y) = kummerRatio σ x * kummerRatio σ y := by
  apply Units.ext
  rw [Units.val_mul]
  rw [kummerRatio_coe, kummerRatio_coe, kummerRatio_coe]
  rw [show ((x * y : Lˣ) : L) = (x : L) * (y : L) from Units.val_mul x y, map_mul]
  exact mul_div_mul_comm _ _ _ _

/-- `kummerRatio` of a unit coming from `K` is trivial. -/
lemma kummerRatio_unitsMap (σ : Gal(L/K)) (c : Kˣ) :
    kummerRatio σ (Units.map (algebraMap K L) c) = 1 := by
  rw [kummerRatio, algEquivUnitsMap_unitsMap]
  exact div_self' _

/-- `kummerRatio` is unchanged when the argument is multiplied by a unit coming from `K`. -/
lemma kummerRatio_mul_unitsMap (σ : Gal(L/K)) (x : Lˣ) (c : Kˣ) :
    kummerRatio σ (x * Units.map (algebraMap K L) c) = kummerRatio σ x := by
  rw [kummerRatio_mul_apply, kummerRatio_unitsMap, mul_one]

end RatioLemmas

section Char

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- The value of the Kummer character, read in `L` through the algebra map; this is the bridge
between `kummerCharacter` (living in `rootsOfUnity n K`) and `kummerRatio` (living in `L`). -/
lemma kummerCharacter_apply_coe (hζ : IsPrimitiveRoot ζ n) (a : kummerSubgroup n K L)
    (σ : Gal(L/K)) :
    algebraMap K L (((kummerCharacter hζ a σ : rootsOfUnity n K) : Kˣ) : K) =
      ((kummerRatio σ (kummerRoot a) : Lˣ) : L) := by
  have h := congrArg (fun u : Lˣ => (u : L)) (map_kummerCharacter_apply hζ a σ)
  rwa [Units.coe_map] at h

/-- Two units of `K` which become equal in `L` are equal. -/
lemma units_eq_of_algebraMap_coe_eq {x y : Kˣ}
    (h : algebraMap K L (x : K) = algebraMap K L (y : K)) : x = y :=
  Units.ext ((algebraMap K L).injective h)

/-- Equal Kummer characters have equal ratios `σ α / α`. -/
lemma kummerRatio_eq_of_kummerCharacter_eq (hζ : IsPrimitiveRoot ζ n)
    (a b : kummerSubgroup n K L) (h : kummerCharacter hζ a = kummerCharacter hζ b)
    (σ : Gal(L/K)) :
    kummerRatio σ (kummerRoot a) = kummerRatio σ (kummerRoot b) := by
  apply Units.ext
  have hσ : kummerCharacter hζ a σ = kummerCharacter hζ b σ := DFunLike.congr_fun h σ
  exact (kummerCharacter_apply_coe hζ a σ).symm.trans
    ((congrArg (fun y : rootsOfUnity n K => algebraMap K L ((y : Kˣ) : K)) hσ).trans
      (kummerCharacter_apply_coe hζ b σ))

/-- Conversely, equal ratios `σ α / α` for all `σ` give equal Kummer characters. -/
lemma kummerCharacter_eq_of_forall_kummerRatio_eq (hζ : IsPrimitiveRoot ζ n)
    (a b : kummerSubgroup n K L)
    (h : ∀ σ : Gal(L/K), kummerRatio σ (kummerRoot a) = kummerRatio σ (kummerRoot b)) :
    kummerCharacter hζ a = kummerCharacter hζ b := by
  refine MonoidHom.ext fun σ => Subtype.ext ?_
  apply units_eq_of_algebraMap_coe_eq (L := L)
  exact (kummerCharacter_apply_coe hζ a σ).trans
    ((congrArg (fun v : Lˣ => (v : L)) (h σ)).trans (kummerCharacter_apply_coe hζ b σ).symm)

/-- If `a / b` is an `n`-th power in `Kˣ`, then the ratios `σ α / α` and `σ β / β` agree: indeed
`β * d` is an `n`-th root of `a` when `d ^ n = a / b`, and the ratio only depends on the `n`-th
power. -/
lemma forall_kummerRatio_eq_of_div_mem (hζ : IsPrimitiveRoot ζ n)
    (a b : kummerSubgroup n K L) (hd : ((a : Kˣ) / (b : Kˣ)) ∈ nthPowerSubgroup n Kˣ)
    (σ : Gal(L/K)) :
    kummerRatio σ (kummerRoot a) = kummerRatio σ (kummerRoot b) := by
  obtain ⟨d, hd'⟩ := hd
  have hγn : (kummerRoot b * Units.map (algebraMap K L) d) ^ n =
      Units.map (algebraMap K L) (a : Kˣ) := by
    rw [mul_pow, kummerRoot_pow b, ← map_pow, hd', map_div]
    exact mul_div_cancel _ _
  have hγL : ((kummerRoot b * Units.map (algebraMap K L) d : Lˣ) : L) ^ n =
      algebraMap K L ((a : Kˣ) : K) := by
    have h := congrArg (fun u : Lˣ => (u : L)) hγn
    rwa [Units.val_pow_eq_pow_val, Units.coe_map] at h
  calc kummerRatio σ (kummerRoot a)
      = kummerRatio σ (kummerRoot b * Units.map (algebraMap K L) d) :=
        kummerRatio_congr hζ hγL (kummerRoot_pow_val a) σ
    _ = kummerRatio σ (kummerRoot b) := by
        rw [kummerRatio_mul_unitsMap]

end Char

section Main

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- If the ratios `σ α / α` agree for all `σ`, then `a / b` is an `n`-th power in `Kˣ`.  This is
the direction which uses that `L/K` is Galois: `α / β` is fixed by `Gal(L/K)`, hence lies in
`Kˣ`. -/
lemma div_mem_of_forall_kummerRatio_eq {n : ℕ} (a b : kummerSubgroup n K L)
    (h : ∀ σ : Gal(L/K), kummerRatio σ (kummerRoot a) = kummerRatio σ (kummerRoot b)) :
    ((a : Kˣ) / (b : Kˣ)) ∈ nthPowerSubgroup n Kˣ := by
  set u : Lˣ := kummerRoot a / kummerRoot b with hudef
  have hfix : ∀ σ : Gal(L/K), (σ : L ≃ₐ[K] L) (u : L) = (u : L) := by
    intro σ
    have hσ : ((kummerRatio σ (kummerRoot a) : Lˣ) : L) =
        ((kummerRatio σ (kummerRoot b) : Lˣ) : L) :=
      congrArg (fun x : Lˣ => (x : L)) (h σ)
    rw [kummerRatio_coe σ (kummerRoot a), kummerRatio_coe σ (kummerRoot b)] at hσ
    rw [div_eq_div_iff (Units.ne_zero (kummerRoot a)) (Units.ne_zero (kummerRoot b))] at hσ
    have hσb : (σ : L ≃ₐ[K] L) (kummerRoot b : L) ≠ 0 := fun h0 =>
      Units.ne_zero (kummerRoot b) ((σ : L ≃ₐ[K] L).injective (by rw [h0, map_zero]))
    rw [hudef, Units.val_div_eq_div_val, map_div₀]
    rw [div_eq_div_iff hσb (Units.ne_zero (kummerRoot b)), hσ]
    exact mul_comm _ _
  obtain ⟨c, hc⟩ := Set.mem_range.mp ((IsGalois.mem_range_algebraMap_iff_fixed (u : L)).mpr hfix)
  have hc0 : c ≠ 0 := by
    intro h0
    have : (u : L) = 0 := by rw [← hc, h0, map_zero]
    exact Units.ne_zero u this
  have hd_eq : Units.map (algebraMap K L) (Units.mk0 c hc0) = u := by
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0]
    exact hc
  have hu_pow : u ^ n = Units.map (algebraMap K L) ((a : Kˣ) / (b : Kˣ)) := by
    rw [hudef, div_pow, kummerRoot_pow a, kummerRoot_pow b, map_div]
  have hu_pow_L : algebraMap K L (((a : Kˣ) / (b : Kˣ) : Kˣ) : K) = ((u : L)) ^ n := by
    have h' := congrArg (fun v : Lˣ => (v : L)) hu_pow
    rw [Units.val_pow_eq_pow_val, Units.coe_map] at h'
    exact h'.symm
  refine ⟨Units.mk0 c hc0, units_eq_of_algebraMap_coe_eq (L := L) ?_⟩
  rw [Units.val_pow_eq_pow_val, map_pow, Units.val_mk0, hc, hu_pow_L]

/-- **The Kummer pairing is injective modulo `n`-th powers.**  For a finite Galois extension
`L/K` and a primitive `n`-th root of unity `ζ ∈ K`, two elements of the Kummer subgroup
`Kˣ ∩ (Lˣ)^n` have the same Kummer character if and only if their quotient is an `n`-th power
in `Kˣ`. -/
theorem kummerCharacter_eq_iff_div_mem {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) (a b : kummerSubgroup n K L) :
    kummerCharacter hζ a = kummerCharacter hζ b ↔
      ((a : Kˣ) / (b : Kˣ)) ∈ nthPowerSubgroup n Kˣ := by
  constructor
  · intro h
    exact div_mem_of_forall_kummerRatio_eq a b
      (fun σ => kummerRatio_eq_of_kummerCharacter_eq hζ a b h σ)
  · intro hd
    exact kummerCharacter_eq_of_forall_kummerRatio_eq hζ a b
      (fun σ => forall_kummerRatio_eq_of_div_mem hζ a b hd σ)

end Main

end Work.Kummer
