import Mathlib
import Submission.Work.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Kummer

universe u v

section RatioMul

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The Kummer ratio is multiplicative in the unit: `σ(αβ)/(αβ) = (σα/α)(σβ/β)`. -/
lemma kummerRatio_mul_units (σ : Gal(L/K)) (α β : Lˣ) :
    kummerRatio σ (α * β) = kummerRatio σ α * kummerRatio σ β := by
  rw [kummerRatio, kummerRatio, kummerRatio, map_mul, mul_div_mul_comm]

end RatioMul

section RootMul

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The product of chosen `n`-th roots of `a` and `b` is an `n`-th root of `a * b`. -/
lemma kummerRoot_mul_pow {n : ℕ} {a b : kummerSubgroup n K L} :
    ((kummerRoot a * kummerRoot b : Lˣ) : L) ^ n =
      algebraMap K L (((a * b : kummerSubgroup n K L) : Kˣ) : K) := by
  rw [Units.val_mul, mul_pow, kummerRoot_pow_val, kummerRoot_pow_val, ← map_mul]
  congr 1

end RootMul

theorem kummerCharacter_mul {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (a b : kummerSubgroup n K L) :
    kummerCharacter hζ (a * b) = kummerCharacter hζ a * kummerCharacter hζ b := by
  ext σ : 1
  rw [MonoidHom.mul_apply]
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  have hf : Function.Injective (Units.map (algebraMap K L : K →* L)) :=
    Units.map_injective (algebraMap K L).injective
  apply (hf.eq_iff).mp
  calc Units.map (algebraMap K L : K →* L)
          (((kummerCharacter hζ (a * b)) σ : rootsOfUnity n K) : Kˣ)
      = kummerRatio σ (kummerRoot (a * b)) := map_kummerCharacter_apply hζ (a * b) σ
    _ = kummerRatio σ (kummerRoot a * kummerRoot b) := by
          rw [kummerRatio_congr hζ (kummerRoot_mul_pow (a := a) (b := b))
            (kummerRoot_pow_val (a * b)) σ]
    _ = kummerRatio σ (kummerRoot a) * kummerRatio σ (kummerRoot b) :=
          kummerRatio_mul_units σ _ _
    _ = Units.map (algebraMap K L : K →* L) (((kummerCharacter hζ a) σ : rootsOfUnity n K) : Kˣ)
        * Units.map (algebraMap K L : K →* L)
            (((kummerCharacter hζ b) σ : rootsOfUnity n K) : Kˣ) := by
          rw [map_kummerCharacter_apply hζ a σ, map_kummerCharacter_apply hζ b σ]
    _ = Units.map (algebraMap K L : K →* L)
          ((((kummerCharacter hζ a) σ : rootsOfUnity n K) : Kˣ)
            * (((kummerCharacter hζ b) σ : rootsOfUnity n K) : Kˣ)) := by
          rw [map_mul]

end Work.Kummer
